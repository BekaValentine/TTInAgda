module ValidityModalDeBruijnToPHOAS where

-- Syntax

infixr 9 _*_
infixr 8 _=>_
data Ty : Set where
  BOOL NAT : Ty
  _*_ _=>_ : Ty → Ty → Ty
  [] : Ty → Ty

infixl 7 _,_
data Context : Set where
  <> : Context
  _,_ : Context → Ty → Context

infix 6 _∋_
data _∋_ : Context → Ty → Set where
  here : ∀ {Γ A} → Γ , A ∋ A
  there : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

infix 6 _/_⊢_
data _/_⊢_ (Δ Γ : Context) : Ty → Set where
  -- A true fragment
  var : ∀ {A} → Γ ∋ A → Δ / Γ ⊢ A
  t f : Δ / Γ ⊢ BOOL
  if : ∀ {C} → Δ / Γ ⊢ BOOL → Δ / Γ ⊢ C → Δ / Γ ⊢ C → Δ / Γ ⊢ C
  z : Δ / Γ ⊢ NAT
  s : Δ / Γ ⊢ NAT → Δ / Γ ⊢ NAT
  rec : ∀ {C} → Δ / Γ ⊢ NAT → Δ / Γ ⊢ C → Δ / Γ , C ⊢ C → Δ / Γ ⊢ C
  _,_ : ∀ {A B} → Δ / Γ ⊢ A → Δ / Γ ⊢ B → Δ / Γ ⊢ A * B
  fst : ∀ {A B} → Δ / Γ ⊢ A * B → Δ / Γ ⊢ A
  snd : ∀ {A B} → Δ / Γ ⊢ A * B → Δ / Γ ⊢ B
  lam : ∀ {A B} → Δ / Γ , A ⊢ B → Δ / Γ ⊢ A => B
  _$_ : ∀ {A B} → Δ / Γ ⊢ A => B → Δ / Γ ⊢ A → Δ / Γ ⊢ B
  
  -- A valid fragment
  var* : ∀ {A} → Δ ∋ A → Δ / Γ ⊢ A
  box : ∀ {A} → Δ / <> ⊢ A → Δ / Γ ⊢ [] A
  unbox : ∀ {A C} → Δ / Γ ⊢ [] A → Δ , A / Γ ⊢ C → Δ / Γ ⊢ C

-- Semantics

postulate
  [_]ty : Ty → Set
  [_]ty* : Ty → Set
  _/_⊩_ : Context → Context → Ty → Set
  uncurry : ∀ {Δ Γ A B} → ([ A ]ty → Δ / Γ ⊩ B) → Δ / Γ , A ⊩ B
  uncurry* : ∀ {Δ Γ A B} → ([ A ]ty* → Δ / Γ ⊩ B) → Δ , A / Γ ⊩ B
  [var] : ∀ {Δ Γ A} → Γ ∋ A → Δ / Γ ⊩ A
  [true] [false] : ∀ {Δ Γ} → Δ / Γ ⊩ BOOL
  [if'] : ∀ {Δ Γ C} → Δ / Γ ⊩ BOOL → Δ / Γ ⊩ C → Δ / Γ ⊩ C → Δ / Γ ⊩ C
  [zero] : ∀ {Δ Γ} → Δ / Γ ⊩ NAT
  [suc] : ∀ {Δ Γ} → Δ / Γ ⊩ NAT → Δ / Γ ⊩ NAT
  [rec'] : ∀ {Δ Γ C} → Δ / Γ ⊩ NAT → Δ / Γ ⊩ C → Δ / Γ , C ⊩ C → Δ / Γ ⊩ C
  _[,]_ : ∀ {Δ Γ A B} → Δ / Γ ⊩ A → Δ / Γ ⊩ B → Δ / Γ ⊩ A * B
  [fst'] : ∀ {Δ Γ A B} → Δ / Γ ⊩ A * B → Δ / Γ ⊩ A
  [snd'] : ∀ {Δ Γ A B} → Δ / Γ ⊩ A * B → Δ / Γ ⊩ B
  [lam] : ∀ {Δ Γ A B} → Δ / Γ , A ⊩ B → Δ / Γ ⊩ A => B
  _[$]_ : ∀ {Δ Γ A B} → Δ / Γ ⊩ A => B → Δ / Γ ⊩ A → Δ / Γ ⊩ B
  [var*] : ∀ {Δ Γ A} → Δ ∋ A → Δ / Γ ⊩ A
  [box] : ∀ {Δ Γ A} → Δ / <> ⊩ A → Δ / Γ ⊩ [] A
  [unbox] : ∀ {Δ Γ A C} → Δ / Γ ⊩ [] A → Δ , A / Γ ⊩ C → Δ / Γ ⊩ C

infix 6 _/_⊩_

eval : ∀ {Δ Γ A} → Δ / Γ ⊢ A → Δ / Γ ⊩ A
eval (var i) = [var] i
eval t = [true]
eval f = [false]
eval (if test cons alt) = [if'] (eval test) (eval cons) (eval alt)
eval z = [zero]
eval (s n) = [suc] (eval n)
eval (rec num zcase scase) = [rec'] (eval num) (eval zcase) (eval scase)
eval (x , y) = eval x [,] eval y
eval (fst p) = [fst'] (eval p)
eval (snd p) = [snd'] (eval p)
eval (lam body) = [lam] (eval body)
eval (fun $ arg) = eval fun [$] eval arg
eval (var* i) = [var*] i
eval (box x) = [box] (eval x)
eval (unbox x body) = [unbox] (eval x) (eval body)

lam2 : ∀ {Δ Γ A B} → ([ A ]ty → Δ / Γ ⊩ B) → Δ / Γ ⊩ A => B
lam2 body = [lam] (uncurry body)

unbox2 : ∀ {Δ Γ A C} → Δ / Γ ⊩ [] A → ([ A ]ty* → Δ / Γ ⊩ C) → Δ / Γ ⊩ C
unbox2 x body = [unbox] x (uncurry* body)
