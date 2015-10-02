{-# OPTIONS --no-positivity-check #-}

module STLC where
  
  data Nat : Set where
    zero : Nat
    suc : Nat → Nat
  
  {-# BUILTIN NATURAL Nat #-}
  {-# BUILTIN ZERO zero #-}
  {-# BUILTIN SUC suc #-}
  
  _+_ : Nat → Nat → Nat
  zero + n = n
  suc m + n = suc (m + n)
  
  data Fin : Nat → Set where
    fzero : ∀ {n} → Fin (suc n)
    fsuc : ∀ {n} → Fin n → Fin (suc n)
  
  roll : ∀ {n} (m : Nat) → Fin (suc (m + n))
  roll zero = fzero
  roll (suc m) = fsuc (roll m)
  
  data Ty : Set where
    _*_ _=>_ : Ty → Ty → Ty
  
  data RawTerm (n : Nat) : Set where
    var : Fin n → RawTerm n
    pair : RawTerm n → RawTerm n → RawTerm n
    fst snd : RawTerm n → RawTerm n
    lam : RawTerm (suc n) → RawTerm n
    app : RawTerm n → RawTerm n → RawTerm n
  
  data Context : Nat → Set where
    <> : Context zero
    _,_ : ∀ {n} → Context n → Ty → Context (suc n)
  
  proj : ∀ {n} → Context n → Fin n → Ty
  proj <> ()
  proj (_ , A) fzero = A
  proj (Γ , _) (fsuc i) = proj Γ i
  
  data _∶_∈_ : ∀ {n} → Fin n → Ty → Context n → Set where
    here : ∀ {n A} {Γ : Context n} → fzero ∶ A ∈ (Γ , A)
    there : ∀ {n A B} {v : Fin n} {Γ : Context n} → v ∶ A ∈ Γ → fsuc v ∶ A ∈ (Γ , B)
  
  remember : ∀ {n} {i : Fin n} {Γ} → i ∶ proj Γ i ∈ Γ
  remember {zero} {()}
  remember {suc n} {fzero} {_ , A} = here
  remember {suc n} {fsuc i} {Γ , _} = there remember
  
  module Normal where
    
    data _⊢_∶_ {n} : Context n → RawTerm n → Ty → Set where
      hyp : ∀ {Γ A} {v : Fin n} → v ∶ A ∈ Γ → Γ ⊢ var v ∶ A
      *I : ∀ {Γ A B M N} → Γ ⊢ M ∶ A → Γ ⊢ N ∶ B → Γ ⊢ pair M N ∶ (A * B)
      *E1 : ∀ {Γ A B P} → Γ ⊢ P ∶ (A * B) → Γ ⊢ fst P ∶ A
      *E2 : ∀ {Γ A B P} → Γ ⊢ P ∶ (A * B) → Γ ⊢ snd P ∶ B
      =>I : ∀ {Γ A B M} → (Γ , A) ⊢ M ∶ B → Γ ⊢ lam M ∶ (A => B)
      =>E : ∀ {Γ A B M N} → Γ ⊢ M ∶ (A => B) → Γ ⊢ N ∶ A → Γ ⊢ app M N ∶ B
    
    v : ∀ {n} (m : Nat) → RawTerm (suc (m + n))
    v m = var (roll m)
    
    h : ∀ {n} (m : Nat) {Γ : Context (suc (m + n))} → Γ ⊢ var (roll m) ∶ proj Γ (roll m)
    h m = hyp remember
    
    flip : ∀ {A B C} → <> ⊢ lam (lam (lam (app (app (v 2) (v 0)) (v 1)))) ∶ ((A => (B => C)) => (B => (A => C)))
    flip = =>I (=>I (=>I (=>E (=>E (h 2) (h 0)) (h 1))))
    
    data Term {n} : Context n → Ty → Set where
      var' : ∀ {Γ A} {v : Fin n} → v ∶ A ∈ Γ → Term Γ A
      pair' : ∀ {Γ A B} → Term Γ A → Term Γ B → Term Γ (A * B)
      fst' : ∀ {Γ A B} → Term Γ (A * B) → Term Γ A
      snd' : ∀ {Γ A B} → Term Γ (A * B) → Term Γ B
      lam' : ∀ {Γ A B} → Term (Γ , A) B → Term Γ (A => B)
      app' : ∀ {Γ A B} → Term Γ (A => B) → Term Γ A → Term Γ B
    
    forget : ∀ {n} {Γ : Context n} {A} → Term Γ A → RawTerm n
    forget (var' {v = v} x) = var v
    forget (pair' x y) = pair (forget x) (forget y)
    forget (fst' p) = fst (forget p)
    forget (snd' p) = snd (forget p)
    forget (lam' b) = lam (forget b)
    forget (app' f x) = app (forget f) (forget x)
    
    reindex : ∀ {n} {Γ : Context n} {A} → (x : Term Γ A) → Γ ⊢ forget x ∶ A
    reindex (var' x) = hyp x
    reindex (pair' x y) = *I (reindex x) (reindex y)
    reindex (fst' p) = *E1 (reindex p)
    reindex (snd' p) = *E2 (reindex p)
    reindex (lam' b) = =>I (reindex b)
    reindex (app' f x) = =>E (reindex f) (reindex x)
  
  module Funny⊢ where
    
    mutual
      data Env : ∀ {n} → Context n → Set where
        <> : Env <>
        _,_ : ∀ {n} {Γ : Context n} {A} → Env Γ → {M : RawTerm 0} → (M ∶ A) → Env (Γ , A)
      
      _⊢_∶_ : ∀ {n} → Context n → RawTerm n → Ty → Set
      Γ ⊢ M ∶ A = Env Γ → M ∶ A
      
      data _∶_ {n} : RawTerm n → Ty → Set where
        hyp : ∀ {Γ A} {v : Fin n} → v ∶ A ∈ Γ → Γ ⊢ var v ∶ A
        *I : ∀ {Γ A B M N} → Γ ⊢ M ∶ A → Γ ⊢ N ∶ B → Γ ⊢ pair M N ∶ (A * B)
        *E1 : ∀ {Γ A B P} → Γ ⊢ P ∶ (A * B) → Γ ⊢ fst P ∶ A
        *E2 : ∀ {Γ A B P} → Γ ⊢ P ∶ (A * B) → Γ ⊢ snd P ∶ B
        =>I : ∀ {Γ A B M} → (Γ , A) ⊢ M ∶ B → Γ ⊢ lam M ∶ (A => B)
        =>E : ∀ {Γ A B M N} → Γ ⊢ M ∶ (A => B) → Γ ⊢ N ∶ A → Γ ⊢ app M N ∶ B
    
    v : ∀ {n} (m : Nat) → RawTerm (suc (m + n))
    v m = var (roll m)
    
    h : ∀ {n} (m : Nat) {Γ : Context (suc (m + n))} → Γ ⊢ var (roll m) ∶ proj Γ (roll m)
    h m = hyp remember
    
    flip : ∀ {A B C} → <> ⊢ lam (lam (lam (app (app (v 2) (v 0)) (v 1)))) ∶ ((A => (B => C)) => (B => (A => C)))
    flip = =>I (=>I (=>I (=>E (=>E (h 2) (h 0)) (h 1))))
    
    data Term {n} : Context n → Ty → Set where
      var' : ∀ {Γ A} {v : Fin n} → v ∶ A ∈ Γ → Term Γ A
      pair' : ∀ {Γ A B} → Term Γ A → Term Γ B → Term Γ (A * B)
      fst' : ∀ {Γ A B} → Term Γ (A * B) → Term Γ A
      snd' : ∀ {Γ A B} → Term Γ (A * B) → Term Γ B
      lam' : ∀ {Γ A B} → Term (Γ , A) B → Term Γ (A => B)
      app' : ∀ {Γ A B} → Term Γ (A => B) → Term Γ A → Term Γ B
    
    forget : ∀ {n} {Γ : Context n} {A} → Term Γ A → RawTerm n
    forget (var' {v = v} x) = var v
    forget (pair' x y) = pair (forget x) (forget y)
    forget (fst' p) = fst (forget p)
    forget (snd' p) = snd (forget p)
    forget (lam' b) = lam (forget b)
    forget (app' f x) = app (forget f) (forget x)
    
    reindex : ∀ {n} {Γ : Context n} {A} → (x : Term Γ A) → Γ ⊢ forget x ∶ A
    reindex (var' x) = hyp x
    reindex (pair' x y) = *I (reindex x) (reindex y)
    reindex (fst' p) = *E1 (reindex p)
    reindex (snd' p) = *E2 (reindex p)
    reindex (lam' b) = =>I (reindex b)
    reindex (app' f x) = =>E (reindex f) (reindex x)
