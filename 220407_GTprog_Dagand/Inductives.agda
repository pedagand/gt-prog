-- * Agda in 5 lines
-- https://agda.readthedocs.io/en/latest/getting-started/index.html

-- This is a comment

{-
  This is a
    multiline
  comment
-}

X : Set₁ -- this is a type declaration
X = Set  -- this is the definition

-- `Set` is the type of all types
-- `Set₁` is the class of all types of all types
-- etc.

-- * Importing the Agda standard library (for simplicity)
-- https://agda.readthedocs.io/en/latest/tools/package-system.html

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List

open import Function

open import Relation.Binary.PropositionalEquality

-- * The Talk

-- "Crocodiles" ? "barbelés" ?
-- https://maartenfokkinga.github.io/utwente/mmf91m.pdf

-- Total functional programming
-- http://sblp2004.ic.uff.br/papers/turner.pdf

-- ** What are inductive types?

data nat : Set where
  ze : nat
  su : nat → nat

data tree : Set where
  leaf : tree
  node : tree → tree → tree

data rose : Set where
  node : List rose → rose
-- https://en.wikipedia.org/wiki/Rose_tree

data ord : Set where
  ze : ⊤            → ord
  su : ord          → ord
  lim : (nat → ord) → ord

-- ** Generic datatypes

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {X Y} → (X → Y) → F X → F Y

open Functor {{...}}


-- We could do this too but I don't recommend it:

{-
record FunctorLaws (F : Set → Set)(F-act : Functor F) : Set₁ where
  field
    fmap-id : ∀ x → fmap id x ≡ x
    fmap-compose : ∀ x f g  → fmap (f ∘ g) x ≡ fmap f (fmap g x)
-}

-- ** The Hard Way (category terrorist-style)

module Cat where

  -- *** "Least" fixpoint

  {-# NO_POSITIVITY_CHECK #-}
  -- Trust me, I'm a doctor
  data μ (F : Set → Set) : Set where
    ctor : (xs : F (μ F)) → μ F

  -- Codata? 
  -- https://dl.acm.org/doi/10.1145/2480359.2429075

  -- Example: Nat
  NatF : Set → Set
  NatF X = ⊤ ⊎ X

  nat' : Set
  nat' = μ NatF

  -- Example: Brouwer ordinals
  OrdF : Set → Set
  OrdF X = ⊤ ⊎ X ⊎ (nat → X)

  ord' : Set
  ord' = μ OrdF

  -- Example: empty set
  bot : Set
  bot = μ (λ X → X)

  -- Puzzle: implement a function of type
  bot-elim : ∀ {A : Set} → bot → A
  bot-elim = {!!}

  -- Careful: there are monsters in that definition:
  evilF : Set → Set
  evilF X = X → X

  evil : Set
  evil = μ evilF

  -- Puzzle: diagonalize `evil` and make inhabitant of the empty type
  evil-wins : evil → ⊥
  evil-wins e = {!!}

  -- *** Algebra

  Alg : (Set → Set) → Set → Set
  Alg F X = F X → X

  -- *** Initial algebra

  {-# NON_TERMINATING #-}
  fold : ∀ {F : Set → Set}{X}{{ _ : Functor F }} → 
         Alg F X → μ F → X
  fold α (ctor xs) = α (fmap (fold α) xs)
 
{-
  subject to commuting square:

     F (μ F) -[ fmap (fold α) ] -> F X
       ^
       |                            |
       | ctor                       | α
       v                            v
      μ F --------[ fold α ]------> X

-}

  -- ref: Lambek Theorem
  -- https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor#LambeksTheorem

  -- Example: computing the length of a list

  data ListF (X : Set) : Set where
    NIL : ListF X
    CONS : ord → X → ListF X

  ListF-map : ∀ {X Y} → (X → Y) → ListF X → ListF Y
  ListF-map f NIL = NIL
  ListF-map f (CONS n x) = CONS n (f x)

  instance
    ListF-Functor : Functor ListF
    ListF-Functor = record { fmap = ListF-map }

  len-alg : Alg ListF nat
  len-alg NIL = ze
  len-alg (CONS a rec-len) = su rec-len

  len : μ ListF → nat
  len = fold len-alg

  -- Example: computing the height of a tree

  data TreeF (X : Set) : Set where
    LEAF : TreeF X
    NODE : X → ord → X → TreeF X

  TreeF-map : ∀ {X Y} → (X → Y) → TreeF X → TreeF Y
  TreeF-map f LEAF = LEAF
  TreeF-map f (NODE l n r) = NODE (f l) n (f r)

  instance
    TreeF-Functor : Functor TreeF
    TreeF-Functor = record { fmap = TreeF-map }

  size-alg : Alg TreeF nat
  size-alg LEAF = ze
  size-alg (NODE size-rec-l o size-rec-r) = su (max size-rec-l size-rec-r)
    where postulate max : nat → nat → nat

  size : μ TreeF → nat
  size = fold size-alg

  -- Q[Adrien]: why not an iso?
  unctor : ∀ {F} → μ F → F (μ F)
  unctor (ctor xs) = xs

  pf-iso-lr : ∀ {F} (x : μ F) → ctor (unctor x) ≡ x
  pf-iso-lr (ctor xs) = refl

  pf-iso-rl : ∀ {F} (xs : F (μ F)) → unctor {F} (ctor xs) ≡ xs
  pf-iso-rl x = refl

  -- Digression: recursion / iteration vs. induction?
  -- More: https://www.irif.fr/~dagand/stuffs/notes/html/InductionFromFold.html
  induction : ∀ {F : Set → Set}{P : μ F → Set}{{ _ : Functor F }} →
              {!!} → (xs : μ F) → P xs
  induction = {!!}


-- ** The Martin-Löf way: W-types

module TT where

  record Sig : Set₁ where
    field
      Op : Set
      Ar : Op → Set

  open Sig public

  ⟦_⟧ : Sig → Set → Set
  ⟦ Σ ⟧ X = Σ[ op ∈ Op Σ ] (Ar Σ op → X)

  ⟦_⟧map : ∀ Σ {X Y} → (X → Y) → ⟦ Σ ⟧ X → ⟦ Σ ⟧ Y
  ⟦ Σ ⟧map f (op , ks) = op , λ ar → f (ks ar)

  instance
    SigFunctor : ∀ {Σ} → Functor ⟦ Σ ⟧
    SigFunctor {Σ} = record { fmap = ⟦ Σ ⟧map }

  data μ (Σ : Sig) : Set where
    ctor : (xs : ⟦ Σ ⟧ (μ Σ)) → μ Σ

  {-# TERMINATING #-} -- This can be removed by specializing `fmap (fold α)`
  fold : ∀ {Σ X} → Cat.Alg ⟦ Σ ⟧ X → μ Σ → X
  fold α (ctor xs) = α (fmap (fold α) xs)

-- ** Haskell / Cedille
-- https://wiki.haskell.org/Catamorphisms

module CoYo where

  {-# NO_UNIVERSE_CHECK #-}
  record CoYoneda (F : Set → Set)(X : Set) : Set where
    constructor ⟨_#_#_⟩
    field
      C : Set
      state : F C
      update : C → X
  -- ≅ ∃ C. F X × (C → X) -- also: codensity

  -- Remark: Yoneda is
  --   F X ≅ ∀ C. (X → C) → F C

  open CoYoneda public

  CoYoneda-map : ∀ {F A B} → (A → B) → CoYoneda F A → CoYoneda F B
  CoYoneda-map f coy = ⟨ C coy # state coy # (λ s → f (update coy s)) ⟩

  instance
    CoYonedaFunctor : ∀ {F} → Functor (CoYoneda F)
    CoYonedaFunctor {F} = record { fmap = CoYoneda-map {F} }

  -- F X ≅ CoYoneda F X
  module Iso where
    fromCoYoneda : ∀ {F X} {{_ : Functor F}} → CoYoneda F X → F X
    fromCoYoneda coy = fmap (update coy) (state coy)

    toCoYoneda : ∀ {F X} → F X → CoYoneda F X
    toCoYoneda {F}{X} fx = record { C = X ; state = fx ; update = id }

  open Cat hiding (fold)

  {-# TERMINATING #-}
  fold : ∀ {F : Set → Set}{X} → Alg (CoYoneda F) X → μ F → X
  fold {F}{X} α (ctor xs) = α ⟨ μ F # xs # fold α ⟩
    -- No more asking for F to be a Functor!

-- * Recursion schemes
-- https://www.cs.tufts.edu/comp/150FP/archive/ralf-hinze/MPC2010.pdf

-- ** Mutual recursion

Set² : Set₁
Set² = Set × Set

Set²[_∶_] : Set² → Set² → Set
Set²[ (C₁ , C₂) ∶ (D₁ , D₂) ] = C₁ → D₁ × C₂ → D₂

module Set² where

  {-# NO_POSITIVITY_CHECK #-}
  data μ₁ (F : Set² → Set²) : Set
  data μ₂ (F : Set² → Set²) : Set

  data μ₁ F where
    ctor₁ : proj₁ (F (μ₁ F , μ₂ F)) → μ₁ F
  data μ₂ F where
    ctor₂ : proj₂ (F (μ₁ F , μ₂ F)) → μ₂ F

  record Alg²  (F : Set² → Set²)(A : Set) : Set₁ where
    field
      rec₁ : ∀ {X Y} → (X → A) → (Y → A) → proj₁ (F (X , Y)) → A
      rec₂ : ∀ {X Y} → (X → A) → (Y → A) → proj₂ (F (X , Y)) → A

  open Alg² public

  {-# TERMINATING #-}
  fold₁ : ∀ {F : Set² → Set²}{A} → Alg² F A → μ₁ F → A
  fold₂ : ∀ {F : Set² → Set²}{A} → Alg² F A → μ₂ F → A

  fold₁ α (ctor₁ x) = rec₁ α (fold₁ α) (fold₂ α) x
  fold₂ α (ctor₂ x) = rec₂ α (fold₁ α) (fold₂ α) x

-- *** Example: rose tree / flatten

module Example-flatten where

  open import Data.Nat

  data ROSE (X Y : Set) : Set where
    NODE : ℕ → Y → ROSE X Y

  data ROSES (X Y : Set) : Set where
    NIL : ROSES X Y
    CONS : X → Y → ROSES X Y

  ROSE-ROSES : Set × Set → Set × Set
  ROSE-ROSES (X , Y) = ROSE X Y , ROSES X Y

  open Set²

  Rose = μ₁ ROSE-ROSES
  Roses = μ₂ ROSE-ROSES

  pattern Node n ts = ctor₁ (NODE n ts)
  pattern Nil = ctor₂ NIL
  pattern Cons t ts = ctor₂ (CONS t ts)

  FLATTEN : Alg² ROSE-ROSES (List ℕ)
  rec₁ FLATTEN flattena flattens (NODE n ts) = n ∷ flattens ts
  rec₂ FLATTEN flattena flattens NIL = []
  rec₂ FLATTEN flattena flattens (CONS t ts) = flattena t ++ flattens ts

  flattena = fold₁ FLATTEN
  flattens = fold₂ FLATTEN

-- ** Parameterized type

record Set^Set : Set₁ where
  field
    ∣_∣ : Set → Set
    _-map_ : ∀ {X Y} → (X → Y) → ∣ X ∣  → ∣ Y ∣

open Set^Set public

Set^Set[_∶_] : Set^Set → Set^Set → Set₁
Set^Set[ P ∶ Q ] = ∀ {X} → ∣ P ∣ X → ∣ Q ∣ X

_⇒_ = Set^Set[_∶_]

_⊗_ : Set^Set → Set^Set → Set^Set
∣_∣ (P ⊗ Q) X = ∣ P ∣ X × ∣ Q ∣ X
_-map_ (P ⊗ Q) f (p , q) = (P -map f) p , (Q -map f) q

Constant : Set → Set^Set
Constant S = record { ∣_∣ = λ _ → S ; _-map_ = λ _ s → s }

module μSet^Set where

  {-# NO_POSITIVITY_CHECK #-}
  data dμ (F : Set^Set → Set^Set)(A : Set) : Set
  {-# TERMINATING #-}
  μ-map : ∀ {F : Set^Set → Set^Set}{X Y} → (X → Y) → dμ F X → dμ F Y
  μ^ : (Set^Set → Set^Set) → Set^Set

  data dμ F A where
    ctor : ∣ F (μ^ F) ∣ A → dμ F A

  μ-map {F} f (ctor x) = ctor (((F (μ^ F)) -map f) x)

  μ^ F = record { ∣_∣ = dμ F
               ; _-map_ = μ-map }

  -- Q: Using Yoneda to get functoriality *)
  Alg : (F : Set^Set → Set^Set) → Set^Set → Set₁
  Alg F Q = ∀ {P} → P ⇒ Q → F P ⇒ Q

  {-# TERMINATING #-}
  fold : ∀ {F P} → Alg F P → μ^ F ⇒ P
  fold {F}{P} f (ctor x) = f (fold {F}{P} f) x

-- *** Example: perfect tree / size

module Example-size where

  open import Data.Nat

  data dPERFECT (X : Set^Set)(A : Set) : Set where
    ZERO : A → dPERFECT X A
    SUCC : ∣ X ∣ (A × A) → dPERFECT X A

  PERFECT-MAP : ∀ {X : Set^Set} {A B} → (A → B) → dPERFECT X A → dPERFECT X B
  PERFECT-MAP f (ZERO x) = ZERO (f x)
  PERFECT-MAP {X} f (SUCC x) = SUCC ( (X -map (λ { (a₁ , a₂) → f a₁ , f a₂ })) x)

  PERFECT : Set^Set → Set^Set
  PERFECT X = record { ∣_∣ = dPERFECT X ; _-map_ = PERFECT-MAP {X} }

  open μSet^Set

  Perfect = μ^ PERFECT

  pattern Zero as = ctor (ZERO as)
  pattern Succ t = ctor (SUCC t)


  SIZE : Alg  PERFECT (Constant ℕ)
  SIZE size (ZERO as) = 1
  SIZE size (SUCC t) = 2 * size t

  size = fold {PERFECT} {Constant ℕ} SIZE


-- * What's left out?

--  - induction
--  - inductive families
--  - comonad & recursion schemes
--    https://www.cambridge.org/core/journals/journal-of-functional-programming/article/unifying-structured-recursion-schemes/2CF2B29B85890E893F9761EA1C3B709E
--  - unfold/coinduction
