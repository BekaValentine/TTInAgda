module DeBruijnToPHOAS where

-- Syntax

infixr 9 _*_
infixr 8 _=>_
data Ty : Set where
  BOOL NAT : Ty
  _*_ _=>_ : Ty → Ty → Ty

infixl 7 _,_
data Context : Set where
  <> : Context
  _,_ : Context → Ty → Context

infix 6 _∋_
data _∋_ : Context → Ty → Set where
  here : ∀ {Γ A} → Γ , A ∋ A
  there : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

infix 6 _⊢_
data _⊢_ (Γ : Context) : Ty → Set where
  var : ∀ {A} → Γ ∋ A → Γ ⊢ A
  t f : Γ ⊢ BOOL
  if : ∀ {C} → Γ ⊢ BOOL → Γ ⊢ C → Γ ⊢ C → Γ ⊢ C
  z : Γ ⊢ NAT
  s : Γ ⊢ NAT → Γ ⊢ NAT
  rec : ∀ {C} → Γ ⊢ NAT → Γ ⊢ C → Γ , C ⊢ C → Γ ⊢ C
  _,_ : ∀ {A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A * B
  fst : ∀ {A B} → Γ ⊢ A * B → Γ ⊢ A
  snd : ∀ {A B} → Γ ⊢ A * B → Γ ⊢ B
  lam : ∀ {A B} → Γ , A ⊢ B → Γ ⊢ A => B
  _$_ : ∀ {A B} → Γ ⊢ A => B → Γ ⊢ A → Γ ⊢ B



-- Semantics Auxiliary Stuff

data Bool : Set where
  true false : Bool

if' : ∀ {A : Set} → Bool → A → A → A
if' true x _ = x
if' false _ y = y

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

rec' : ∀ {A : Set} → Nat → A → (A → A) → A
rec' zero ze _ = ze
rec' (suc n) ze su = su (rec' n ze su)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst' : ∀ {A B : Set} → A × B → A
fst' (x , _) = x

snd' : ∀ {A B : Set} → A × B → B
snd' (_ , y) = y


module SemanticsV1 where
  
  -- This version gives the standard semantics for the STLC by interping to Agda
  
  [_]ty : Ty → Set
  [ BOOL ]ty = Bool
  [ NAT ]ty = Nat
  [ A * B ]ty = [ A ]ty × [ B ]ty
  [ A => B ]ty = [ A ]ty → [ B ]ty
  
  data Env : Context → Set where
    <> : Env <>
    _,_ : ∀ {Γ A} → Env Γ → [ A ]ty → Env (Γ , A)
  
  lookup : ∀ {Γ A} → Γ ∋ A → Env Γ → [ A ]ty
  lookup here (_ , x) = x
  lookup (there i) (e , _) = lookup i e
  
  [_]ctx : Context → Set
  [ Γ ]ctx = Env Γ
  
  infix 6 _⊩_
  _⊩_ : Context → Ty → Set
  Γ ⊩ A = [ Γ ]ctx → [ A ]ty
  
  eval : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A
  eval (var i) e = lookup i e
  eval t _ = true
  eval f _ = false
  eval (if test cons alt) e = if' (eval test e) (eval cons e) (eval alt e)
  eval z _ = zero
  eval (s n) e = suc (eval n e)
  eval (rec num zcase scase) e = rec' (eval num e) (eval zcase e) (λ r → eval scase (e , r))
  eval (x , y) e = eval x e , eval y e
  eval (fst p) e = fst' (eval p e)
  eval (snd p) e = snd' (eval p e)
  eval (lam body) e = λ x → eval body (e , x)
  eval (fun $ arg) e = eval fun e (eval arg e)
  
  lam2 : ∀ {Γ A B} → ([ A ]ty → Γ ⊩ B) → Γ ⊩ A => B
  lam2 body e x = body x e


module SemanticsV2  where
  
  -- This version gives the same semantics, but with [_]ty abstracted over (postulated).
  -- This has the consequence of forcing the entire syntax to be recapitulated in the
  -- semantics of [_]ty
  
  postulate
    [_]ty : Ty → Set
    [true] [false] : [ BOOL ]ty
    [if'] : ∀ {C} → [ BOOL ]ty → [ C ]ty → [ C ]ty → [ C ]ty
    [zero] : [ NAT ]ty
    [suc] : [ NAT ]ty → [ NAT ]ty
    [rec'] : ∀ {C} → [ NAT ]ty → [ C ]ty → ([ C ]ty → [ C ]ty) → [ C ]ty
    _[,]_ : ∀ {A B} → [ A ]ty → [ B ]ty → [ A * B ]ty
    [fst'] : ∀ {A B} → [ A * B ]ty → [ A ]ty
    [snd'] : ∀ {A B} → [ A * B ]ty → [ B ]ty
    [lam] : ∀ {A B} → ([ A ]ty → [ B ]ty) → [ A => B ]ty
    _[$]_ : ∀ {A B} → [ A => B ]ty → [ A ]ty → [ B ]ty
  
  data Env : Context → Set where
    <> : Env <>
    _,_ : ∀ {Γ A} → Env Γ → [ A ]ty → Env (Γ , A)
  
  lookup : ∀ {Γ A} → Γ ∋ A → Env Γ → [ A ]ty
  lookup here (_ , x) = x
  lookup (there i) (e , _) = lookup i e
  
  [_]ctx : Context → Set
  [ Γ ]ctx = Env Γ
  
  infix 6 _⊩_
  _⊩_ : Context → Ty → Set
  Γ ⊩ A = [ Γ ]ctx → [ A ]ty
  
  eval : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A
  eval (var i) e = lookup i e
  eval t _ = [true]
  eval f _ = [false]
  eval (if test cons alt) e = [if'] (eval test e) (eval cons e) (eval alt e)
  eval z _ = [zero]
  eval (s n) e = [suc] (eval n e)
  eval (rec num zcase scase) e = [rec'] (eval num e) (eval zcase e) (λ r → eval scase (e , r))
  eval (x , y) e = eval x e [,] eval y e
  eval (fst p) e = [fst'] (eval p e)
  eval (snd p) e = [snd'] (eval p e)
  eval (lam body) e = [lam] (λ x → eval body (e , x))
  eval (fun $ arg) e = eval fun e [$] eval arg e
  
  lam2 : ∀ {Γ A B} → ([ A ]ty → Γ ⊩ B) → Γ ⊩ A => B
  lam2 body e = [lam] (λ x → body x e)

module SemanticsV3  where
  
  -- This version goes further and abstracts over [_]ctx. Doing this forces us to
  -- recapitulate the _,_ constructor for environments at the semantic level as _[,,]_
  -- and we can fold the lookup into the meaning of [var]
  
  postulate
    [_]ty : Ty → Set
    [_]ctx : Context → Set
    [var] : ∀ {Γ A} → Γ ∋ A → [ Γ ]ctx → [ A ]ty
    [true] [false] : [ BOOL ]ty
    [if'] : ∀ {C} → [ BOOL ]ty → [ C ]ty → [ C ]ty → [ C ]ty
    [zero] : [ NAT ]ty
    [suc] : [ NAT ]ty → [ NAT ]ty
    [rec'] : ∀ {C} → [ NAT ]ty → [ C ]ty → ([ C ]ty → [ C ]ty) → [ C ]ty
    _[,]_ : ∀ {A B} → [ A ]ty → [ B ]ty → [ A * B ]ty
    [fst'] : ∀ {A B} → [ A * B ]ty → [ A ]ty
    [snd'] : ∀ {A B} → [ A * B ]ty → [ B ]ty
    [lam] : ∀ {A B} → ([ A ]ty → [ B ]ty) → [ A => B ]ty
    _[$]_ : ∀ {A B} → [ A => B ]ty → [ A ]ty → [ B ]ty
    _[,,]_ : ∀ {Γ A} → [ Γ ]ctx → [ A ]ty → [ Γ , A ]ctx
  
  infix 6 _⊩_
  _⊩_ : Context → Ty → Set
  Γ ⊩ A = [ Γ ]ctx → [ A ]ty
  
  eval : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A
  eval (var i) e = [var] i e
  eval t _ = [true]
  eval f _ = [false]
  eval (if test cons alt) e = [if'] (eval test e) (eval cons e) (eval alt e)
  eval z _ = [zero]
  eval (s n) e = [suc] (eval n e)
  eval (rec num zcase scase) e = [rec'] (eval num e) (eval zcase e) (λ r → eval scase (e [,,] r))
  eval (x , y) e = eval x e [,] eval y e
  eval (fst p) e = [fst'] (eval p e)
  eval (snd p) e = [snd'] (eval p e)
  eval (lam body) e = [lam] (λ x → eval body (e [,,] x))
  eval (fun $ arg) e = eval fun e [$] eval arg e
  
  lam2 : ∀ {Γ A B} → ([ A ]ty → Γ ⊩ B) → Γ ⊩ A => B
  lam2 body e = [lam] (λ x → body x e)

module SemanticsV4  where
  
  -- This version goes further and abstracts _⊩_ entirely, eliminating [_]ty and [_]ctx
  -- This makes things a bit simpler, but it also makes them more powerful, because now
  -- the meta-level semantics is indexed by contexts not just types. This could be good.
  
  postulate
    _⊩_ : Context → Ty → Set
    [var] : ∀ {Γ A} → Γ ∋ A → Γ ⊩ A
    [true] [false] : ∀ {Γ} → Γ ⊩ BOOL
    [if'] : ∀ {Γ C} → Γ ⊩ BOOL → Γ ⊩ C → Γ ⊩ C → Γ ⊩ C
    [zero] : ∀ {Γ} → Γ ⊩ NAT
    [suc] : ∀ {Γ} → Γ ⊩ NAT → Γ ⊩ NAT
    [rec'] : ∀ {Γ C} → Γ ⊩ NAT → Γ ⊩ C → Γ , C ⊩ C → Γ ⊩ C
    _[,]_ : ∀ {Γ A B} → Γ ⊩ A → Γ ⊩ B → Γ ⊩ A * B
    [fst'] : ∀ {Γ A B} → Γ ⊩ A * B → Γ ⊩ A
    [snd'] : ∀ {Γ A B} → Γ ⊩ A * B → Γ ⊩ B
    [lam] : ∀ {Γ A B} → Γ , A ⊩ B → Γ ⊩ A => B
    _[$]_ : ∀ {Γ A B} → Γ ⊩ A => B → Γ ⊩ A → Γ ⊩ B
  
  infix 6 _⊩_
  
  eval : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A
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
  
  -- Unfortunately we now can't implement our convenient form of lam,
  -- because we can't even write the type b/c [ A ]ty is nonsense
  -- lam2 : ∀ {Γ A B} → ([ A ]ty → Γ ⊩ B) → Γ ⊩ A => B

module SemanticsV5  where
  
  -- This version brings back [_]ty to fix the previous problem, and relies
  -- crucially on the `uncurry` assumption which relates meta-entailment → to
  -- object-entailment ⊩. with careful control of these relations, we can avoid
  -- the unintended modal non-theorem   A ⊩ [] A
  -- 
  -- This relation between meta and object entailment is exactly where the problem
  -- arises in the modal attempts from before. This way, however, we can have
  -- two flavors of [_]ty in the modal version, one for `A true` and one for `A valid`
  -- and relate them to their respective contexts with normal and modal uncurries.
  -- 
  -- The fact that Agda or Haskell might conflate modal and normal proofs doesnt
  -- force the object language to, it just means that Agda and Haskell are an extension
  -- of the modal version, like how Classical Logic is an extension of Intuistic Logic
  
  postulate
    [_]ty : Ty → Set
    _⊩_ : Context → Ty → Set
    uncurry : ∀ {Γ A B} → ([ A ]ty → Γ ⊩ B) → Γ , A ⊩ B
    [var] : ∀ {Γ A} → Γ ∋ A → Γ ⊩ A
    [true] [false] : ∀ {Γ} → Γ ⊩ BOOL
    [if'] : ∀ {Γ C} → Γ ⊩ BOOL → Γ ⊩ C → Γ ⊩ C → Γ ⊩ C
    [zero] : ∀ {Γ} → Γ ⊩ NAT
    [suc] : ∀ {Γ} → Γ ⊩ NAT → Γ ⊩ NAT
    [rec'] : ∀ {Γ C} → Γ ⊩ NAT → Γ ⊩ C → Γ , C ⊩ C → Γ ⊩ C
    _[,]_ : ∀ {Γ A B} → Γ ⊩ A → Γ ⊩ B → Γ ⊩ A * B
    [fst'] : ∀ {Γ A B} → Γ ⊩ A * B → Γ ⊩ A
    [snd'] : ∀ {Γ A B} → Γ ⊩ A * B → Γ ⊩ B
    [lam] : ∀ {Γ A B} → Γ , A ⊩ B → Γ ⊩ A => B
    _[$]_ : ∀ {Γ A B} → Γ ⊩ A => B → Γ ⊩ A → Γ ⊩ B
  
  infix 6 _⊩_
  
  eval : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A
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
  
  -- With [_]ty back, this is fine.
  lam2 : ∀ {Γ A B} → ([ A ]ty → Γ ⊩ B) → Γ ⊩ A => B
  lam2 body = [lam] (uncurry body)
