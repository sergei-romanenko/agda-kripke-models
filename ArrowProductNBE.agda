module ArrowProductNBE (Proposition : Set) where

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

-- Source language: natural deduction

data _⊢_ : List Formula → Formula → Set where
  hyp : ∀ {Γ p} → (p ∷ Γ) ⊢ p
  wkn : ∀ {Γ p q} → Γ ⊢ p → (q ∷ Γ) ⊢ p
  lam : ∀ {Γ p q} → (p ∷ Γ) ⊢ q → Γ ⊢ (p ⊃ q)
  app : ∀ {Γ p q} → Γ ⊢ (p ⊃ q) → Γ ⊢ p → Γ ⊢ q
  pair : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ q → Γ ⊢ (p ∧ q)
  fst : ∀ {Γ p q} → Γ ⊢ (p ∧ q) → Γ ⊢ p
  snd : ∀ {Γ p q} → Γ ⊢ (p ∧ q) → Γ ⊢ q

-- Target language: natural deduction allowing only beta-normal forms

mutual

  data _⊢ʳ_ : List Formula → Formula → Set where
    ne : ∀ {Γ p} → Γ ⊢ᵉ p → Γ ⊢ʳ p
    lam : ∀ {Γ p q} → (p ∷ Γ) ⊢ʳ q → Γ ⊢ʳ (p ⊃ q)
    pair : ∀ {Γ p q} → Γ ⊢ʳ p → Γ ⊢ʳ q → Γ ⊢ʳ (p ∧ q)

  data _⊢ᵉ_ : List Formula → Formula → Set where
    hyp : ∀ {Γ p} → (p ∷ Γ) ⊢ᵉ p
    wkn : ∀ {Γ p q} → Γ ⊢ʳ p → (q ∷ Γ) ⊢ᵉ p
    app : ∀ {Γ p q} → Γ ⊢ᵉ (p ⊃ q) → Γ ⊢ʳ p → Γ ⊢ᵉ q
    fst : ∀ {Γ p q} → Γ ⊢ᵉ (p ∧ q) → Γ ⊢ᵉ p
    snd : ∀ {Γ p q} → Γ ⊢ᵉ (p ∧ q) → Γ ⊢ᵉ q

module SampleProofs (a b c : Formula) where

  a⊃a : [] ⊢ (a ⊃ a)
  a⊃a = lam hyp

  a-b-a : [] ⊢ (a ⊃ (b ⊃ a))
  a-b-a = lam (lam (wkn hyp)) 

  a-ab-b : [] ⊢ (a ⊃ ((a ⊃ b) ⊃ b))
  a-ab-b = lam (lam (app hyp (wkn hyp)))

  a∧b⊃b∧a : [] ⊢ ((a ∧ b) ⊃ (b ∧ a))
  a∧b⊃b∧a = lam (pair (snd hyp) (fst hyp))

  ∧-assoc : [] ⊢ (((a ∧ b) ∧ c) ⊃ (a ∧ (b ∧ c)))
  ∧-assoc = lam (pair (fst (fst hyp)) (pair (snd (fst hyp)) (snd hyp)))

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

-- Worlds (Kripke structures)

record Kripke : Set₁ where
  field
    K : Set
    _≤_ : K → K → Set
    ≤-refl : {w : K} → w ≤ w
    _●_ : {w w′ w′′ : K} → w ≤ w′ → w′ ≤ w′′ → w ≤ w′′
    _⊩ᵃ_ : K → Proposition → Set
    ⊩ᵃ-≤ : {P : Proposition} {w w′ : K} → w ≤ w′ → w ⊩ᵃ P → w′ ⊩ᵃ P

module Soundness (kripke : Kripke) where

  open Kripke kripke

  _⊩_ : K → Formula → Set
  w ⊩ ⟪ a ⟫ = w ⊩ᵃ a
  w ⊩ (p ⊃ q) = {w′ : K} → w ≤ w′ → w′ ⊩ p → w′ ⊩ q
  w ⊩ (p ∧ q) = (w ⊩ p) × (w ⊩ q)

  _⊪_ : K → List Formula → Set
  w ⊪ [] = ⊤
  w ⊪ (p ∷ Γ) = (w ⊩ p) × (w ⊪ Γ)

  ⊩-≤ : ∀ p {w w′ : K} → w ≤ w′ → w ⊩ p → w′ ⊩ p
  ⊩-≤ ⟪ a ⟫ = ⊩ᵃ-≤
  ⊩-≤ (p ⊃ q) w≤w′ w⊩p⊃q w′≤w′′ =
    w⊩p⊃q (w≤w′ ● w′≤w′′)
  ⊩-≤ (p ∧ q) w≤w′ =
    Prod.map (⊩-≤ p w≤w′) (⊩-≤ q w≤w′)

  ⊪-≤ : ∀ Γ {w w′ : K} → w ≤ w′ → w ⊪ Γ → w′ ⊪ Γ
  ⊪-≤ [] w≤w′ w⊪[] = tt
  ⊪-≤ (p ∷ Γ) w≤w′ =
    Prod.map (⊩-≤ p w≤w′) (⊪-≤ Γ w≤w′)

  soundness : ∀ {Γ p} → Γ ⊢ p → {w : K} → w ⊪ Γ → w ⊩ p
  soundness hyp w⊪p∷Γ =
    proj₁ w⊪p∷Γ
  soundness (wkn Γ⊢p) w⊪p∷Γ =
    soundness Γ⊢p (proj₂ w⊪p∷Γ)
  soundness {Γ} (lam Γ⊢p) w⊪Γ w≤w′ w′⊩p =
    soundness Γ⊢p (w′⊩p , ⊪-≤ Γ w≤w′ w⊪Γ)
  soundness (app Γ⊢p⊃q Γ⊢p) w⊪Γ =
    soundness Γ⊢p⊃q w⊪Γ ≤-refl (soundness Γ⊢p w⊪Γ)
  soundness (pair Γ⊢p Γ⊢q) w⊪Γ =
    soundness Γ⊢p w⊪Γ , soundness Γ⊢q w⊪Γ
  soundness (fst Γ⊢p∧q) w⊪Γ =
    proj₁ (soundness Γ⊢p∧q w⊪Γ)
  soundness (snd Γ⊢p∧q) w⊪Γ =
    proj₂ (soundness Γ⊢p∧q w⊪Γ)

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
                 _●_ = ≼-trans;
                 _⊩ᵃ_ = λ Γ a → Γ ⊢ʳ ⟪ a ⟫;
                 ⊩ᵃ-≤ = ⊢ʳ-≼ }

  open Kripke uks
  open Soundness uks

  mutual
    reify : ∀ {Γ} p → Γ ⊩ p → Γ ⊢ʳ p
    reify ⟪ a ⟫ Γ⊩⟪a⟫ = Γ⊩⟪a⟫
    reify (p ⊃ q) Γ⊩p⊃q =
      lam (reify q (Γ⊩p⊃q (≼-cons ≼-refl) (reflect p hyp)))
    reify (p ∧ q) Γ⊩p∧q =
      pair (reify p (proj₁ Γ⊩p∧q)) (reify q (proj₂ Γ⊩p∧q))

    reflect : ∀ {Γ} p → Γ ⊢ᵉ p → Γ ⊩ p
    reflect ⟪ a ⟫ Γ⊢ᵉ⟪a⟫ = ne Γ⊢ᵉ⟪a⟫
    reflect {Γ} (p ⊃ q) Γ⊢ᵉp⊃q Γ≼Γ′ Γ′⊩p =
      reflect q (app (⊢ᵉ-≼ Γ≼Γ′ Γ⊢ᵉp⊃q) (reify p Γ′⊩p))
    reflect (p ∧ q) Γ⊢ᵉp∧q =
      reflect p (fst Γ⊢ᵉp∧q) , reflect q (snd Γ⊢ᵉp∧q)

    reflect-context : (Γ : List Formula) → Γ ⊪ Γ
    reflect-context [] = tt
    reflect-context (p ∷ Γ) =
      reflect p hyp , ⊪-≤ Γ (≼-cons ≼-refl) (reflect-context Γ)

  nbe : ∀ {Γ p} → Γ ⊢ p → Γ ⊢ʳ p
  nbe {Γ} {p} Γ⊢p = reify p (soundness Γ⊢p (reflect-context Γ))
