module ArrowProductSum-CBN (Proposition : Set) where

open import Data.List
open import Data.Unit
  hiding(_≤_)
open import Data.Empty
open import Data.Product as Prod
open import Data.Sum as Sum

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

infix 3 _⊢_
infixr 4 _⊃_
infixr 6 _∧_
infixr 5 _∨_

-- Syntax

data Formula : Set where
  ⟪_⟫  : (a : Proposition) → Formula
  _⊃_ : (p q : Formula) → Formula
  _∧_ : (p q : Formula) → Formula
  _∨_ : (p q : Formula) → Formula

Ctx = List Formula

data _⊢_ : Ctx → Formula → Set where
  hyp : ∀ {Γ p} → p ∷ Γ ⊢ p
  wkn : ∀ {Γ p q} → Γ ⊢ p → q ∷ Γ ⊢ p
  lam  : ∀ {Γ p q} → p ∷ Γ ⊢ q → Γ ⊢ p ⊃ q
  app  : ∀ {Γ p q} → Γ ⊢ p ⊃ q → Γ ⊢ p → Γ ⊢ q
  pair : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ q → Γ ⊢ p ∧ q
  fst : ∀ {Γ p q} → Γ ⊢ p ∧ q → Γ ⊢ p
  snd : ∀ {Γ p q} → Γ ⊢ p ∧ q → Γ ⊢ q
  inl : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ p ∨ q
  inr : ∀ {Γ p q} → Γ ⊢ q → Γ ⊢ p ∨ q
  case : ∀ {Γ p q r} → Γ ⊢ p ∨ q → p ∷ Γ ⊢ r → q ∷ Γ ⊢ r → Γ ⊢ r

module SampleProofs (a b c : Formula) where

  a⊃a : [] ⊢ (a ⊃ a)
  a⊃a = lam hyp

  a-b-a : [] ⊢ (a ⊃ (b ⊃ a))
  a-b-a = lam (lam (wkn hyp)) 

  a-ab-b : [] ⊢ (a ⊃ ((a ⊃ b) ⊃ b))
  a-ab-b = lam (lam (app hyp (wkn hyp)))

  a∧b⊃b∧a : [] ⊢ ((a ∧ b) ⊃ (b ∧ a))
  a∧b⊃b∧a = lam (pair (snd hyp) (fst hyp))

  a∨b⊃b∨a : [] ⊢ ((a ∨ b) ⊃ (b ∨ a))
  a∨b⊃b∨a = lam (case hyp (inr hyp) (inl hyp))

  ∧-assoc : [] ⊢ (((a ∧ b) ∧ c) ⊃ (a ∧ (b ∧ c)))
  ∧-assoc = lam (pair (fst (fst hyp)) (pair (snd (fst hyp)) (snd hyp)))

  [a∨b]⊃[a⊃c]⊃[b⊃c]⊃c : [] ⊢ ((a ∨ b) ⊃ ((a ⊃ c) ⊃ ((b ⊃ c) ⊃ c)))
  [a∨b]⊃[a⊃c]⊃[b⊃c]⊃c =
    lam (lam (lam
      (case (wkn (wkn hyp)) (app (wkn (wkn hyp)) hyp) (app (wkn hyp) hyp))))

-- Worlds (Kripke structures)

record Kripke : Set₁ where
  field
    World : Set
    _≤_ : World → World → Set
    ε : ∀ {w} → w ≤ w
    _⊙_ : ∀ {w w′ w′′} → w ≤ w′ → w′ ≤ w′′ → w ≤ w′′
    _⊩ᵃ_ : World → Formula → Set
    ⊩ᵃ-≤ : ∀ {a w w′} → w ≤ w′ → w ⊩ᵃ ⟪ a ⟫ → w′ ⊩ᵃ ⟪ a ⟫

module Soundness (kripke : Kripke) where

  open Kripke kripke

  infix 3 _⊩ˢ_ _⊩_ _⊪_

  mutual

    _⊩ˢ_ : World → Formula → Set
    w ⊩ˢ ⟪ a ⟫ = w ⊩ᵃ ⟪ a ⟫
    w ⊩ˢ p ⊃ q = ∀ {w′} → w ≤ w′ → w′ ⊩ p → w′ ⊩ q
    w ⊩ˢ p ∧ q = w ⊩ p × w ⊩ q
    w ⊩ˢ p ∨ q = w ⊩ p ⊎ w ⊩ q

    _⊩_ : World → Formula → Set
    w ⊩ p = (r : Formula) →
      ∀ {w′} → w ≤ w′ →
      (∀ {w′′} → w′ ≤ w′′ → w′′ ⊩ˢ p → w′′ ⊩ᵃ r) →
      w′ ⊩ᵃ r

  _⊪_ : World → Ctx → Set
  w ⊪ [] = ⊤
  w ⊪ (p ∷ Γ) = w ⊩ p × w ⊪ Γ

  ⊩-≤ : ∀ p {w w′} → w ≤ w′ → w ⊩ p → w′ ⊩ p
  ⊩-≤ p ≤′ w⊩p r ≤′′ k = w⊩p r (≤′ ⊙ ≤′′) k

  ⊩ˢ-≤ : ∀ p {w w′} → w ≤ w′ → w ⊩ˢ p → w′ ⊩ˢ p
  ⊩ˢ-≤ ⟪ a ⟫ = ⊩ᵃ-≤
  ⊩ˢ-≤ (p ⊃ q) ≤′ w⊩ˢp⊃q ≤′′ =
    w⊩ˢp⊃q (≤′ ⊙ ≤′′)
  ⊩ˢ-≤ (p ∧ q) ≤′ =
    Prod.map (⊩-≤ p ≤′) (⊩-≤ q ≤′)
  ⊩ˢ-≤ (p ∨ q) ≤′ =
    Sum.map (⊩-≤ p ≤′) (⊩-≤ q ≤′)

  ⊪-≤ : ∀ Γ {w w′} → w ≤ w′ → w ⊪ Γ → w′ ⊪ Γ
  ⊪-≤ [] ≤′ tt = tt
  ⊪-≤ (p ∷ Γ) ≤′ =
    Prod.map (⊩-≤ p ≤′) (⊪-≤ Γ ≤′)

  return : ∀ p {w} → w ⊩ˢ p → w ⊩ p
  return p w⊩ˢp r ≤′ k =
    k ε (⊩ˢ-≤ p ≤′ w⊩ˢp)

  bind : ∀ p r {w} → w ⊩ p → (∀ {w′} → w ≤ w′ → w′ ⊩ˢ p → w′ ⊩ r) → w ⊩ r
  bind p r w⊩p k r′ ≤′ k′ =
    w⊩p r′ ≤′
      (λ ≤′′ w′′⊩ˢp → k (≤′ ⊙ ≤′′) w′′⊩ˢp r′ ε
        (λ ≤′′′ → k′ (≤′′ ⊙ ≤′′′)))

  soundness : ∀ {Γ p} → Γ ⊢ p → ∀ {w} → w ⊪ Γ → w ⊩ p
  soundness hyp (w⊩p , w⊪Γ) =
    w⊩p
  soundness (wkn Γ⊢p) (w⊩q , w⊪Γ) =
    soundness Γ⊢p w⊪Γ
  soundness (lam {Γ} {p} {q} p∷Γ⊢q) w⊪Γ =
    return (p ⊃ q) (λ ≤′ w′⊩p → soundness p∷Γ⊢q (w′⊩p , ⊪-≤ Γ ≤′ w⊪Γ))
  soundness (app {Γ} {p} {q} Γ⊢p⊃q Γ⊢p) w⊪Γ =
    bind (p ⊃ q) q (soundness Γ⊢p⊃q w⊪Γ)
      (λ ≤′ kpq → kpq ε (soundness Γ⊢p (⊪-≤ Γ ≤′ w⊪Γ)))
  soundness (pair {Γ} {p} {q} Γ⊢p Γ⊢q) {w} w⊪Γ =
    return (p ∧ q) (soundness Γ⊢p w⊪Γ , soundness Γ⊢q w⊪Γ)
  soundness (fst {Γ} {p} {q} Γ⊢p∧q) w⊪Γ =
    bind (p ∧ q) p (soundness Γ⊢p∧q w⊪Γ) (λ ≤′ w′⊩p∧q → proj₁ w′⊩p∧q)
  soundness (snd {Γ} {p} {q} Γ⊢p∧q) {w} w⊪Γ =
    bind (p ∧ q) q (soundness Γ⊢p∧q w⊪Γ) (λ ≤′ w′⊩p∧q → proj₂ w′⊩p∧q)
  soundness (inl {Γ} {p} {q} Γ⊢p) {w} w⊪Γ =
    return (p ∨ q) (inj₁ (soundness Γ⊢p w⊪Γ))
  soundness (inr {Γ} {p} {q} Γ⊢q) {w} w⊪Γ =
    return (p ∨ q) (inj₂ (soundness Γ⊢q w⊪Γ))
  soundness (case {Γ} {p} {q} {r} Γ⊢p∨q p∷Γ⊢r q∷Γ⊢r) {w} w⊪Γ =
    bind (p ∨ q) r (soundness Γ⊢p∨q w⊪Γ)
      (λ ≤′ → [ (λ w′⊩p → soundness p∷Γ⊢r (w′⊩p , ⊪-≤ Γ ≤′ w⊪Γ)) ,
                 (λ w′⊩q → soundness q∷Γ⊢r (w′⊩q , ⊪-≤ Γ ≤′ w⊪Γ)) ]′)

module Completeness where

  data _≼_ : (Γ Γ′ : Ctx) → Set where 
    ≼-refl : ∀ {Γ} → Γ ≼ Γ
    ≼-cons : ∀ {Γ Γ′ p} → Γ ≼ Γ′ → Γ ≼ (p ∷ Γ′)

  ≼-trans : ∀ {Γ Γ′ Γ′′} → Γ ≼ Γ′ → Γ′ ≼ Γ′′ → Γ ≼ Γ′′
  ≼-trans Γ≼Γ′ ≼-refl = Γ≼Γ′
  ≼-trans Γ≼Γ′ (≼-cons Γ′≼Γ′′) = ≼-cons (≼-trans Γ≼Γ′ Γ′≼Γ′′)

  δ : ∀ {Γ p} → Γ ≼ (p ∷ Γ)
  δ = ≼-cons ≼-refl

  ⊢-≼ : ∀ {p Γ Γ′} → Γ ≼ Γ′ → Γ ⊢ p → Γ′ ⊢ p
  ⊢-≼ ≼-refl Γ′⊢p = Γ′⊢p
  ⊢-≼ (≼-cons Γ≼Γ′) Γ⊢p = wkn (⊢-≼ Γ≼Γ′ Γ⊢p)

  uks : Kripke
  uks = record
    { World = Ctx
    ; _≤_ = _≼_
    ; ε = ≼-refl
    ; _⊙_ = ≼-trans
    ; _⊩ᵃ_ = _⊢_
    ; ⊩ᵃ-≤ = ⊢-≼
    }

  open Kripke uks
  open Soundness uks

  mutual

    reify : ∀ {p Γ} → Γ ⊩ p → Γ ⊢ p
    reify {⟪ a ⟫} Γ⊩⟪a⟫ =
      Γ⊩⟪a⟫ ⟪ a ⟫ ε (λ Γ≼Γ′ Γ′⊩ᵃ⟪a⟫ → Γ′⊩ᵃ⟪a⟫)
    reify {p ⊃ q} Γ⊩p⊃q =
      Γ⊩p⊃q (p ⊃ q) ε (λ Γ≼Γ′ kpq →
        lam (reify (kpq (≼-cons ε) (reflect hyp))) )
    reify {p ∧ q} Γ⊩p∧q =
      Γ⊩p∧q (p ∧ q) ε
        (λ Γ≼Γ′ Γ′⊩p∧q →
          pair (reify (proj₁ Γ′⊩p∧q)) (reify (proj₂ Γ′⊩p∧q)))
    reify {p ∨ q} Γ⊩p∨q =
      Γ⊩p∨q (p ∨ q) ε (λ Γ≼Γ′ →
        [ (λ Γ′⊩p → inl (reify Γ′⊩p)) , (λ Γ′⊩q → inr (reify Γ′⊩q)) ]′)

    reflect : ∀ {p Γ} → Γ ⊢ p → Γ ⊩ p
    reflect {⟪ a ⟫} Γ⊢⟪a⟫ r Γ≼Γ′ k =
      k ε (⊢-≼ Γ≼Γ′ Γ⊢⟪a⟫)
    reflect {p ⊃ q} Γ⊢p⊃q r Γ≼Γ′ k =
      k ε (λ Γ′≼Γ′′ Γ′′⊩p →
        reflect (app (⊢-≼ (Γ≼Γ′ ⊙ Γ′≼Γ′′) Γ⊢p⊃q) (reify Γ′′⊩p)))
    reflect {p ∧ q} Γ⊢p∧q r Γ≼Γ′ k =
      k ε
        (reflect (fst Γ′⊢p∧q) , reflect (snd Γ′⊢p∧q))
      where Γ′⊢p∧q = ⊢-≼ Γ≼Γ′ Γ⊢p∧q
    reflect {p ∨ q} Γ⊢p∨q r {Γ′} Γ≼Γ′ k =
      case Γ′⊢p∨q
          (k δ (inj₁ (reflect hyp)))
          (k δ (inj₂ (reflect hyp)))
      where Γ′⊢p∨q = ⊢-≼ Γ≼Γ′ Γ⊢p∨q

  reflect-context : ∀ Γ → Γ ⊪ Γ
  reflect-context [] = tt
  reflect-context (p ∷ Γ) =
    reflect hyp , ⊪-≤ Γ δ (reflect-context Γ)

  nbe : ∀ {Γ p} → Γ ⊢ p → Γ ⊢ p
  nbe {Γ} Γ⊢p = reify (soundness Γ⊢p (reflect-context Γ))

  {-
  -- disjunction property

  disjunction-prop : ∀ {Γ p q} → Γ ⊢ (p ∨ q) → (Γ ⊢ p) ⊎ (Γ ⊢ q)
  disjunction-prop {Γ} {p} {q} Γ⊢p∨q
    with soundness Γ⊢p∨q (reflect-context Γ)
  ... | xxx = {!xxx ? !}
  -}

module NBE-Samples (a b c d : Proposition) where

  open Completeness

  id-id : [] ⊢ (⟪ a ⟫ ⊃ ⟪ a ⟫)
  id-id = app (lam hyp) (lam hyp)

  nbe-id-id : nbe id-id ≡ lam hyp
  nbe-id-id = refl

  fst-pair : [] ⊢ (⟪ a ⟫ ⊃ (⟪ b ⟫ ⊃ ⟪ a ⟫))
  fst-pair = lam (lam (fst (pair (wkn hyp) hyp)))

  nbe-fst-pair : nbe fst-pair ≡ lam (lam (wkn hyp))
  nbe-fst-pair = refl

  case-inl : [] ⊢ (⟪ a ⟫ ⊃ ⟪ a ⟫)
  case-inl = lam (case (inl hyp) hyp hyp)

  nbe-case-inl : nbe case-inl ≡ lam hyp
  nbe-case-inl = refl
