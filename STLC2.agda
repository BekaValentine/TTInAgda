module STLC2 where

  data Nat : Set where
    zero : Nat
    suc : Nat → Nat
  
  {-# BUILTIN NATURAL Nat #-}
  {-# BUILTIN ZERO zero #-}
  {-# BUILTIN SUC suc #-}
  
  _+_ : Nat → Nat → Nat
  zero + n = n
  suc m + n = suc (m + n)
  
  _+'_ : Nat → Nat → Nat
  m +' zero = m
  m +' suc n = suc (m +' n)
  
  data Fin : Nat → Set where
    fzero : ∀ {n} → Fin (suc n)
    fsuc : ∀ {n} → Fin n → Fin (suc n)
  
  roll : ∀ {n} (m : Nat) → Fin (suc (m + n))
  roll zero = fzero
  roll (suc m) = fsuc (roll m)
  
  data Ty : Set where
    _*_ _=>_ : Ty → Ty → Ty
  
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
    
    data RawTerm (n : Nat) : Set where
      var : Fin n → RawTerm n
      pair : RawTerm n → RawTerm n → RawTerm n
      fst snd : RawTerm n → RawTerm n
      lam : RawTerm (suc n) → RawTerm n
      app : RawTerm n → RawTerm n → RawTerm n
    
    data _⊢_true {n} : Context n → Ty → Set where
      hyp : ∀ {Γ A} {v : Fin n} → v ∶ A ∈ Γ → Γ ⊢ A true
      *I : ∀ {Γ A B} → Γ ⊢ A true → Γ ⊢ B true → Γ ⊢ (A * B) true
      *E1 : ∀ {Γ A B} → Γ ⊢ (A * B) true → Γ ⊢ A true
      *E2 : ∀ {Γ A B} → Γ ⊢ (A * B) true → Γ ⊢ B true
      =>I : ∀ {Γ A B} → (Γ , A) ⊢ B true → Γ ⊢ (A => B) true
      =>E : ∀ {Γ A B} → Γ ⊢ (A => B) true → Γ ⊢ A true → Γ ⊢ B true
    
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
    
    forget : ∀ {n} {Γ : Context n} {A} → Γ ⊢ A true → RawTerm n
    forget (hyp {v = v} x) = var v
    forget (*I px py) = pair (forget px) (forget py)
    forget (*E1 pp) = fst (forget pp)
    forget (*E2 pp) = snd (forget pp)
    forget (=>I pb) = lam (forget pb)
    forget (=>E pf px) = app (forget pf) (forget px)
    
    reindex : ∀ {n} {Γ : Context n} {A} → (p : Γ ⊢ A true) → Γ ⊢ forget p ∶ A
    reindex (hyp x) = hyp x
    reindex (*I px py) = *I (reindex px) (reindex py)
    reindex (*E1 pp) = *E1 (reindex pp)
    reindex (*E2 pp) = *E2 (reindex pp)
    reindex (=>I pb) = =>I (reindex pb)
    reindex (=>E pf px) = =>E (reindex pf) (reindex px)
    
    forget' : ∀ {n} {Γ : Context n} {M A} → Γ ⊢ M ∶ A → Γ ⊢ A true
    forget' (hyp x) = hyp x
    forget' (*I px py) = *I (forget' px) (forget' py)
    forget' (*E1 pp) = *E1 (forget' pp)
    forget' (*E2 pp) = *E2 (forget' pp)
    forget' (=>I pb) = =>I (forget' pb)
    forget' (=>E pf px) = =>E (forget' pf) (forget' px)
  
  module Funny⊢ (S : Set) (_true₀ : Ty → Set) (_∶₀_ : S → Ty → Set) where
    
    data RawValue : Set where
      var : S → RawValue
      pair : RawValue → RawValue → RawValue
      lam : (S → RawValue) → RawValue
    
    data RawEnv : Nat → Set where
      <> : RawEnv 0
      _,_ : ∀ {n} → RawEnv n → S → RawEnv (suc n)
    
    rawLookup : ∀ {n} → Fin n → RawEnv n → S
    rawLookup fzero (_ , x) = x
    rawLookup (fsuc i) (e , _) = rawLookup i e
    
    _⊢r_ : Nat → Set → Set
    n ⊢r J = RawEnv n → J
      
    data RawTerm : Set where
      var : S → RawTerm
      pair : RawTerm → RawTerm → RawTerm
      fst : RawTerm → RawTerm
      snd : RawTerm → RawTerm
      lam : (S → RawTerm) → RawTerm
      app : RawTerm → RawTerm → RawTerm
    
    valToTerm : RawValue → RawTerm
    valToTerm (var x) = var x
    valToTerm (pair x y) = pair (valToTerm x) (valToTerm y)
    valToTerm (lam b) = lam (λ s → valToTerm (b s))
    
    var! : ∀ {n} → Fin n → n ⊢r RawTerm
    var! i e = var (rawLookup i e)
    
    pair! : ∀ {n} → n ⊢r RawTerm → n ⊢r RawTerm → n ⊢r RawTerm
    pair! px py e = pair (px e) (py e)
    
    fst! : ∀ {n} → n ⊢r RawTerm → n ⊢r RawTerm
    fst! pp e = fst (pp e)
    
    snd! : ∀ {n} → n ⊢r RawTerm → n ⊢r RawTerm
    snd! pp e = snd (pp e)
    
    lam! : ∀ {n} → suc n ⊢r RawTerm → n ⊢r RawTerm
    lam! pb e = lam (λ s → pb (e , s))
    
    app! : ∀ {n} → n ⊢r RawTerm → n ⊢r RawTerm → n ⊢r RawTerm
    app! pf px e = app (pf e) (px e)


    data PropEnv : {n : Nat} → Context n → Set where
      <> : PropEnv <>
      _,_ : ∀ {n A} {Γ : Context n} → PropEnv Γ → A true₀ → PropEnv (Γ , A)
    
    data _∋_ : ∀ {n} → Context n → Ty → Set where
      here : ∀ {n} {Γ : Context n} {A} → (Γ , A) ∋ A
      there : ∀ {n} {Γ : Context n} {A B} → Γ ∋ A → (Γ , B) ∋ A
    
    lower : ∀ {n A} {Γ : Context n} → Γ ∋ A → Fin n
    lower here = fzero
    lower (there i) = fsuc (lower i)
    
    _⊢p_ : ∀ {n} → Context n → Set → Set
    Γ ⊢p J = PropEnv Γ → J
    
    data _true : Ty → Set where
      hyp : ∀ {A} → A true₀ → A true
      *I : ∀ {A B} → A true → B true → (A * B) true
      *E1 : ∀ {A B} → (A * B) true → A true
      *E2 : ∀ {A B} → (A * B) true → B true
      =>I : ∀ {A B} → (A true₀ → B true) → (A => B) true
      =>E : ∀ {A B} → (A => B) true → A true → B true
    
    hypp! : ∀ {n A} {Γ : Context n} → Γ ∋ A → Γ ⊢p A true
    hypp! here (_ , p) = hyp p
    hypp! (there i) (e , _) = hypp! i e
    
    *Ip! : ∀ {n A B} {Γ : Context n} → Γ ⊢p A true → Γ ⊢p B true → Γ ⊢p (A * B) true
    *Ip! px py e = *I (px e) (py e)
    
    *E1p! : ∀ {n A B} {Γ : Context n} → Γ ⊢p (A * B) true → Γ ⊢p A true
    *E1p! pp e = *E1 (pp e)
    
    *E2p! : ∀ {n A B} {Γ : Context n} → Γ ⊢p (A * B) true → Γ ⊢p B true
    *E2p! pp e = *E2 (pp e)
    
    =>Ip! : ∀ {n A B} {Γ : Context n} → (Γ , A) ⊢p B true → Γ ⊢p (A => B) true
    =>Ip! pb e = =>I (λ s → pb (e , s))
    
    =>Ep! : ∀ {n A B} {Γ : Context n} → Γ ⊢p (A => B) true → Γ ⊢p A true → Γ ⊢p B true
    =>Ep! pf px e = =>E (pf e) (px e)
    
    
    data Env : ∀ {n} → Context n → Set where
      <> : Env <>
      _,_∶_ : ∀ {n} {Γ : Context n} {A} → Env Γ → ∀ s → s ∶₀ A → Env (Γ , A)
    
    data _∶_ : RawTerm → Ty → Set where
      hyp : ∀ {s A} → s ∶₀ A → var s ∶ A
      *I : ∀ {A B M N} → M ∶ A → N ∶ B → pair M N ∶ (A * B)
      *E1 : ∀ {A B P} → P ∶ (A * B) → fst P ∶ A
      *E2 : ∀ {A B P} → P ∶ (A * B) → snd P ∶ B
      =>I : ∀ {A B M} → (∀ s → s ∶₀ A → M s ∶ B) → lam M ∶ (A => B)
      =>E : ∀ {A B M N} → M ∶ (A => B) → N ∶ A → app M N ∶ B
    
    envToRawEnv : ∀ {n} {Γ : Context n} → Env Γ → RawEnv n
    envToRawEnv <> = <>
    envToRawEnv (e , s ∶ _) = envToRawEnv e , s
    
    [_]_ : ∀ {n} {Γ : Context n} → Env Γ → (RawEnv n → RawTerm) → RawTerm 
    [ e ] M = M (envToRawEnv e)
    
    _⊢_∶_ : ∀ {n} (Γ : Context n) → (RawEnv n → RawTerm) → Ty → Set
    Γ ⊢ M ∶ A = (e : Env Γ) → ([ e ] M) ∶ A
    
    hyp! : ∀ {n A} {Γ : Context n} → (i : Γ ∋ A) → Γ ⊢ var! (lower i) ∶ A
    hyp! here (e , s ∶ p) = hyp p
    hyp! (there i) (e , _ ∶ _) = hyp! i e
    
    *I! : ∀ {n A B} {Γ : Context n} {M N : RawEnv n → RawTerm} → Γ ⊢ M ∶ A → Γ ⊢ N ∶ B → Γ ⊢ pair! M N ∶ (A * B)
    *I! px py e = *I (px e) (py e)
    
    *E1! : ∀ {n A B} {Γ : Context n} {P : RawEnv n → RawTerm} → Γ ⊢ P ∶ (A * B) → Γ ⊢ fst! P ∶ A
    *E1! pp e = *E1 (pp e)
    
    *E2! : ∀ {n A B} {Γ : Context n} {P : RawEnv n → RawTerm} → Γ ⊢ P ∶ (A * B) → Γ ⊢ snd! P ∶ B
    *E2! pp e = *E2 (pp e)
    
    =>I! : ∀ {n A B} {Γ : Context n} {M : RawEnv (suc n) → RawTerm} → (Γ , A) ⊢ M ∶ B → Γ ⊢ lam! M ∶ (A => B)
    =>I! pb e = =>I (λ s p → pb (e , s ∶ p))
