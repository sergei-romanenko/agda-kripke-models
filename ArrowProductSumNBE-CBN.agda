module ArrowProductSumNBE-CBN (Proposition : Set) where

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

----------
-- Syntax
----------

data Formula : Set where
  ⟪_⟫  : (a : Proposition) → Formula
  _⊃_ : (p q : Formula) → Formula
  _∧_ : (p q : Formula) → Formula
  _∨_ : (p q : Formula) → Formula

data _⊢_ : List Formula → Formula → Set where
  hyp : ∀ {Γ p} → (p ∷ Γ) ⊢ p
  wkn : ∀ {Γ p q} → Γ ⊢ p → (q ∷ Γ) ⊢ p
  lam  : ∀ {Γ p q} → (p ∷ Γ) ⊢ q → Γ ⊢ (p ⊃ q)
  app  : ∀ {Γ p q} → Γ ⊢ (p ⊃ q) → Γ ⊢ p → Γ ⊢ q
  pair : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ q → Γ ⊢ (p ∧ q)
  fst : ∀ {Γ p q} → Γ ⊢ (p ∧ q) → Γ ⊢ p
  snd : ∀ {Γ p q} → Γ ⊢ (p ∧ q) → Γ ⊢ q
  inl : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ (p ∨ q)
  inr : ∀ {Γ p q} → Γ ⊢ q → Γ ⊢ (p ∨ q)
  case : ∀ {Γ p q r} → Γ ⊢ (p ∨ q) → (p ∷ Γ) ⊢ r → (q ∷ Γ) ⊢ r → Γ ⊢ r

-- Target language: natural deduction allowing only beta-normal forms

mutual

  data _⊢ʳ_ : List Formula → Formula → Set where
    ne : ∀ {Γ p} → Γ ⊢ᵉ p → Γ ⊢ʳ p
    lam : ∀ {Γ p q} → (p ∷ Γ) ⊢ʳ q → Γ ⊢ʳ (p ⊃ q)
    pair : ∀ {Γ p q} → Γ ⊢ʳ p → Γ ⊢ʳ q → Γ ⊢ʳ (p ∧ q)
    inl : ∀ {Γ p q} → Γ ⊢ʳ p → Γ ⊢ʳ (p ∨ q)
    inr : ∀ {Γ p q} → Γ ⊢ʳ q → Γ ⊢ʳ (p ∨ q)

  data _⊢ᵉ_ : List Formula → Formula → Set where
    hyp : ∀ {Γ p} → (p ∷ Γ) ⊢ᵉ p
    wkn : ∀ {Γ p q} → Γ ⊢ʳ p → (q ∷ Γ) ⊢ᵉ p
    app : ∀ {Γ p q} → Γ ⊢ᵉ (p ⊃ q) → Γ ⊢ʳ p → Γ ⊢ᵉ q
    fst : ∀ {Γ p q} → Γ ⊢ᵉ (p ∧ q) → Γ ⊢ᵉ p
    snd : ∀ {Γ p q} → Γ ⊢ᵉ (p ∧ q) → Γ ⊢ᵉ q
    case : ∀ {Γ p q r} → Γ ⊢ᵉ (p ∨ q) → (p ∷ Γ) ⊢ʳ r → (q ∷ Γ) ⊢ʳ r → Γ ⊢ᵉ r

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

module SampleProofsR (a b c : Formula) where

  a⊃a : [] ⊢ʳ (a ⊃ a)
  a⊃a = lam (ne hyp)

  a-b-a : [] ⊢ʳ (a ⊃ (b ⊃ a))
  a-b-a = lam (lam (ne (wkn (ne hyp))))

  a-ab-b : [] ⊢ʳ (a ⊃ ((a ⊃ b) ⊃ b))
  a-ab-b = lam (lam (ne (app hyp (ne (wkn (ne hyp))))))

  a∧b⊃b∧a : [] ⊢ ((a ∧ b) ⊃ (b ∧ a))
  a∧b⊃b∧a = lam (pair (snd hyp) (fst hyp))

  ∧-assoc : [] ⊢ʳ (((a ∧ b) ∧ c) ⊃ (a ∧ (b ∧ c)))
  ∧-assoc = lam (pair (ne (fst (fst hyp)))
                      (pair (ne (snd (fst hyp))) (ne (snd hyp))))

  [a∨b]⊃[a⊃c]⊃[b⊃c]⊃c : [] ⊢ʳ ((a ∨ b) ⊃ ((a ⊃ c) ⊃ ((b ⊃ c) ⊃ c)))
  [a∨b]⊃[a⊃c]⊃[b⊃c]⊃c =
    lam (lam (lam
      (ne (case (wkn (ne (wkn (ne hyp))))
                (ne (app (wkn (ne (wkn (ne hyp)))) (ne hyp)))
                (ne (app (wkn (ne hyp)) (ne hyp)))))))

-- Worlds (Kripke structures)

record Kripke : Set₁ where
  field
    K : Set
    _≤_ : K → K → Set
    ≤-refl : {w : K} → w ≤ w
    _⊙_ : {w w′ w′′ : K} → w ≤ w′ → w′ ≤ w′′ → w ≤ w′′
    _⊩ᵃ_ : K → Formula → Set
    ⊩ᵃ-≤ : {a : Proposition} {w w′ : K} → w ≤ w′ → w ⊩ᵃ ⟪ a ⟫ → w′ ⊩ᵃ ⟪ a ⟫

module Soundness (kripke : Kripke) where

  open Kripke kripke

  mutual

    _⊩ˢ_ : K → Formula → Set
    w ⊩ˢ ⟪ a ⟫ = w ⊩ᵃ ⟪ a ⟫
    w ⊩ˢ (p ⊃ q) = {w′ : K} → w ≤ w′ → w′ ⊩ p → w′ ⊩ q
    w ⊩ˢ (p ∧ q) = (w ⊩ p) × (w ⊩ q)
    w ⊩ˢ (p ∨ q) = (w ⊩ p) ⊎ (w ⊩ q)

    _⊩_ : K → Formula → Set
    w ⊩ p = (r : Formula) →
      ∀ {w′} → w ≤ w′ →
      (∀ {w′′} → w′ ≤ w′′ → w′′ ⊩ˢ p → w′′ ⊩ᵃ r) →
      w′ ⊩ᵃ r

  _⊪_ : K → List Formula → Set
  w ⊪ [] = ⊤
  w ⊪ (p ∷ Γ) = (w ⊩ p) × (w ⊪ Γ)

  ⊩-≤ : ∀ p {w w′ : K} → w ≤ w′ → w ⊩ p → w′ ⊩ p
  ⊩-≤ p w≤w′ w⊩p r w′≤w′′ k = w⊩p r (w≤w′ ⊙ w′≤w′′) k

  ⊩ˢ-≤ : ∀ p {w w′ : K} → w ≤ w′ → w ⊩ˢ p → w′ ⊩ˢ p
  ⊩ˢ-≤ ⟪ a ⟫ = ⊩ᵃ-≤
  ⊩ˢ-≤ (p ⊃ q) w≤w′ w⊩ˢp⊃q w′≤w′′ =
    w⊩ˢp⊃q (w≤w′ ⊙ w′≤w′′)
  ⊩ˢ-≤ (p ∧ q) w≤w′ =
    Prod.map (⊩-≤ p w≤w′) (⊩-≤ q w≤w′)
  ⊩ˢ-≤ (p ∨ q) w≤w′ =
    Sum.map (⊩-≤ p w≤w′) (⊩-≤ q w≤w′)

  ⊪-≤ : ∀ Γ {w w′ : K} → w ≤ w′ → w ⊪ Γ → w′ ⊪ Γ
  ⊪-≤ [] w≤w′ tt = tt
  ⊪-≤ (p ∷ Γ) w≤w′ =
    Prod.map (⊩-≤ p w≤w′) (⊪-≤ Γ w≤w′)

  return : ∀ p {w} → w ⊩ˢ p → w ⊩ p
  return p w⊩ˢp r w≤w′ k =
    k ≤-refl (⊩ˢ-≤ p w≤w′ w⊩ˢp)

  bind : ∀ p q {w} → w ⊩ p → (∀ {w′} → w ≤ w′ → w′ ⊩ˢ p → w′ ⊩ q) → w ⊩ q
  bind p q w⊩p k r w≤w′ k′ =
    w⊩p r w≤w′
      (λ w′≤w′′ w′′⊩ˢp → k (w≤w′ ⊙ w′≤w′′) w′′⊩ˢp r ≤-refl
        (λ w′′≤w′′′ → k′ (w′≤w′′ ⊙ w′′≤w′′′)))

  soundness : ∀ {Γ p} → Γ ⊢ p → {w : K} → w ⊪ Γ → w ⊩ p
  soundness hyp (w⊩p , w⊪Γ) =
    w⊩p
  soundness (wkn Γ⊢p) (w⊩q , w⊪Γ) =
    soundness Γ⊢p w⊪Γ
  soundness (lam {Γ} {p} {q} p∷Γ⊢q) w⊪Γ =
    return (p ⊃ q) (λ w≤w′ w′⊩p → soundness p∷Γ⊢q (w′⊩p , ⊪-≤ Γ w≤w′ w⊪Γ))
  soundness (app {Γ} {p} {q} Γ⊢p⊃q Γ⊢p) w⊪Γ =
    bind (p ⊃ q) q (soundness Γ⊢p⊃q w⊪Γ)
      (λ w≤w′ kpq → kpq ≤-refl (soundness Γ⊢p (⊪-≤ Γ w≤w′ w⊪Γ)))
  soundness (pair {Γ} {p} {q} Γ⊢p Γ⊢q) {w} w⊪Γ =
    return (p ∧ q) (soundness Γ⊢p w⊪Γ , soundness Γ⊢q w⊪Γ)
  soundness (fst {Γ} {p} {q} Γ⊢p∧q) w⊪Γ =
    bind (p ∧ q) p (soundness Γ⊢p∧q w⊪Γ) (λ w≤w′ w′⊩p∧q → proj₁ w′⊩p∧q)
  soundness (snd {Γ} {p} {q} Γ⊢p∧q) {w} w⊪Γ =
    bind (p ∧ q) q (soundness Γ⊢p∧q w⊪Γ) (λ w≤w′ w′⊩p∧q → proj₂ w′⊩p∧q)
  soundness (inl {Γ} {p} {q} Γ⊢p) {w} w⊪Γ =
    return (p ∨ q) (inj₁ (soundness Γ⊢p w⊪Γ))
  soundness (inr {Γ} {p} {q} Γ⊢q) {w} w⊪Γ =
    return (p ∨ q) (inj₂ (soundness Γ⊢q w⊪Γ))
  soundness (case {Γ} {p} {q} {r} Γ⊢p∨q p∷Γ⊢r q∷Γ⊢r) {w} w⊪Γ =
    bind (p ∨ q) r (soundness Γ⊢p∨q w⊪Γ)
      (λ {w′} w≤w′ → [ (λ w′⊩p → soundness p∷Γ⊢r (w′⊩p , ⊪-≤ Γ w≤w′ w⊪Γ)) ,
                       (λ w′⊩q → soundness q∷Γ⊢r (w′⊩q , ⊪-≤ Γ w≤w′ w⊪Γ)) ]′)

module Completeness where

  data _≼_ : (Γ Γ′ : List Formula) → Set where 
    ≼-refl : ∀ {Γ} → Γ ≼ Γ
    ≼-cons : ∀ {Γ Γ′ p} → Γ ≼ Γ′ → Γ ≼ (p ∷ Γ′)

  ≼-trans : ∀ {Γ Γ′ Γ′′} → Γ ≼ Γ′ → Γ′ ≼ Γ′′ → Γ ≼ Γ′′
  ≼-trans Γ≼Γ′ ≼-refl = Γ≼Γ′
  ≼-trans Γ≼Γ′ (≼-cons Γ′≼Γ′′) = ≼-cons (≼-trans Γ≼Γ′ Γ′≼Γ′′)

  ⊢ᵉ-≼ : ∀ {p Γ Γ′} → Γ ≼ Γ′ → Γ ⊢ᵉ p → Γ′ ⊢ᵉ p
  ⊢ᵉ-≼ ≼-refl Γ′⊢ᵉp = Γ′⊢ᵉp
  ⊢ᵉ-≼ (≼-cons Γ≼Γ′) Γ⊢ᵉp = wkn (ne (⊢ᵉ-≼ Γ≼Γ′ Γ⊢ᵉp))

  ⊢ʳ-≼ : ∀ {p Γ Γ′} → Γ ≼ Γ′ → Γ ⊢ʳ p → Γ′ ⊢ʳ p
  ⊢ʳ-≼ ≼-refl Γ⊢ʳp = Γ⊢ʳp
  ⊢ʳ-≼ (≼-cons Γ≼Γ′) Γ⊢ʳp = ne (wkn (⊢ʳ-≼ Γ≼Γ′ Γ⊢ʳp))

  uks : Kripke
  uks = record { K = List Formula;
                 _≤_ = _≼_;
                 ≤-refl = ≼-refl;
                 _⊙_ = ≼-trans;
                 _⊩ᵃ_ = _⊢ʳ_;
                 ⊩ᵃ-≤ = ⊢ʳ-≼ }

  open Kripke uks
  open Soundness uks

  mutual

    reify : ∀ {Γ} p → Γ ⊩ p → Γ ⊢ʳ p
    reify ⟪ a ⟫ Γ⊩⟪a⟫ =
      Γ⊩⟪a⟫ ⟪ a ⟫ ≼-refl (λ Γ≼Γ′ Γ′⊩ᵃ⟪a⟫ → Γ′⊩ᵃ⟪a⟫)
    reify (p ⊃ q) Γ⊩p⊃q =
      Γ⊩p⊃q (p ⊃ q) ≼-refl (λ Γ≼Γ′ kpq →
        lam (reify q (kpq (≼-cons ≼-refl) (reflect p hyp))) )
    reify (p ∧ q) Γ⊩p∧q =
      Γ⊩p∧q (p ∧ q) ≤-refl
        (λ Γ≼Γ′ Γ′⊩p∧q →
          pair (reify p (proj₁ Γ′⊩p∧q)) (reify q (proj₂ Γ′⊩p∧q)))
    reify (p ∨ q) Γ⊩p∨q =
      Γ⊩p∨q (p ∨ q) ≼-refl (λ Γ≼Γ′ →
        [ (λ Γ′⊩p → inl (reify p Γ′⊩p)) , (λ Γ′⊩q → inr (reify q Γ′⊩q)) ]′)

    reflect : ∀ {Γ} p → Γ ⊢ᵉ p → Γ ⊩ p
    reflect ⟪ a ⟫ Γ⊢ᵉ⟪p⟫ r Γ≼Γ′ k =
      k ≼-refl (ne (⊢ᵉ-≼ Γ≼Γ′ Γ⊢ᵉ⟪p⟫))
    reflect (p ⊃ q) Γ⊢ᵉp⊃q r Γ≼Γ′ k =
      k ≼-refl (λ Γ′≼Γ′′ Γ′′⊩p →
        reflect q (app (⊢ᵉ-≼ (Γ≼Γ′ ⊙ Γ′≼Γ′′) Γ⊢ᵉp⊃q) (reify p Γ′′⊩p)))
    reflect (p ∧ q) Γ⊢ᵉp∧q r Γ≼Γ′ k =
      k ≼-refl
        (reflect p (fst Γ′⊢ᵉp∧q) , reflect q (snd Γ′⊢ᵉp∧q))
      where Γ′⊢ᵉp∧q = ⊢ᵉ-≼ Γ≼Γ′ Γ⊢ᵉp∧q
    reflect (p ∨ q) Γ⊢ᵉp∨q r {Γ′} Γ≼Γ′ k =
      ne (case (⊢ᵉ-≼ Γ≼Γ′ Γ⊢ᵉp∨q)
               (k (≼-cons ≼-refl) (inj₁ (reflect p hyp)))
               (k (≼-cons ≼-refl) (inj₂ (reflect q hyp))))

  reflect-context : (Γ : List Formula) → Γ ⊪ Γ
  reflect-context [] = tt
  reflect-context (p ∷ Γ) =
    reflect p hyp , ⊪-≤ Γ (≼-cons ≼-refl) (reflect-context Γ)

  nbe : ∀ {Γ p} → Γ ⊢ p → Γ ⊢ʳ p
  nbe {Γ} {p} Γ⊢p = reify p (soundness Γ⊢p (reflect-context Γ))
