module ArrowProduct (Proposition : Set) where

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

data _⊢_ : List Formula → Formula → Set where
  hyp : ∀ {Γ p} → (p ∷ Γ) ⊢ p
  wkn : ∀ {Γ p q} → Γ ⊢ p → (q ∷ Γ) ⊢ p
  lam  : ∀ {Γ p q} → (p ∷ Γ) ⊢ q → Γ ⊢ (p ⊃ q)
  app  : ∀ {Γ p q} → Γ ⊢ (p ⊃ q) → Γ ⊢ p → Γ ⊢ q
  pair : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ q → Γ ⊢ (p ∧ q)
  fst : ∀ {Γ p q} → Γ ⊢ (p ∧ q) → Γ ⊢ p
  snd : ∀ {Γ p q} → Γ ⊢ (p ∧ q) → Γ ⊢ q

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

-- Worlds (Kripke structures)

record Kripke : Set₁ where
  field
    K : Set
    _≤_ : K → K → Set
    ≤-refl : {w : K} → w ≤ w
    ≤-trans : {w₁ w₂ w₃ : K} → w₁ ≤ w₂ → w₂ ≤ w₃ → w₁ ≤ w₃
    _⊩ᵃ_ : K → Proposition → Set
    ⊩ᵃ-≤ : {P : Proposition} {w₁ w₂ : K} → w₁ ≤ w₂ → w₁ ⊩ᵃ P → w₂ ⊩ᵃ P

module Soundness (kripke : Kripke) where

  open Kripke kripke

  _⊩_ : K → Formula → Set
  w ⊩ ⟪ a ⟫ = w ⊩ᵃ a
  w ⊩ (p ⊃ q) = {w' : K} → w ≤ w' → w' ⊩ p → w' ⊩ q
  w ⊩ (p ∧ q) = (w ⊩ p) × (w ⊩ q)

  ⊩-≤ : ∀ p {w w′ : K} → w ≤ w′ → w ⊩ p → w′ ⊩ p
  ⊩-≤ ⟪ a ⟫ = ⊩ᵃ-≤
  ⊩-≤ (p ⊃ q) w≤w′ w⊩p⊃q w′≤w′′ =
    w⊩p⊃q (≤-trans w≤w′ w′≤w′′)
  ⊩-≤ (p ∧ q) w≤w′ =
    Prod.map (⊩-≤ p w≤w′) (⊩-≤ q w≤w′)

  _⊪_ : K → List Formula → Set
  w ⊪ [] = ⊤
  w ⊪ (p ∷ Γ) = (w ⊩ p) × (w ⊪ Γ)

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

  ⊢-≼ : ∀ {p Γ Γ′} → Γ ≼ Γ′ → Γ ⊢ p → Γ′ ⊢ p
  ⊢-≼ ≼-refl Γ′⊢p = Γ′⊢p
  ⊢-≼ (≼-cons Γ≼Γ′) Γ⊢p = wkn (⊢-≼ Γ≼Γ′ Γ⊢p)

  uks : Kripke
  uks = record { K = List Formula;
                 _≤_ = _≼_;
                 ≤-refl = ≼-refl;
                 ≤-trans = ≼-trans;
                 _⊩ᵃ_ = λ Γ a → Γ ⊢ ⟪ a ⟫;
                 ⊩ᵃ-≤ = ⊢-≼ }

  open Kripke uks
  open Soundness uks

  mutual
    reify : ∀ {Γ} p → Γ ⊩ p → Γ ⊢ p
    reify ⟪ a ⟫ Γ⊩⟪a⟫ = Γ⊩⟪a⟫
    reify (p ⊃ q) Γ⊩p⊃q =
      lam (reify q (Γ⊩p⊃q (≼-cons ≼-refl) (reflect p hyp)))
    reify (p ∧ q) (Γ⊩p , Γ⊩q) =
      pair (reify p Γ⊩p) (reify q Γ⊩q)

    reflect : ∀ {Γ} p → Γ ⊢ p → Γ ⊩ p
    reflect ⟪ a ⟫ Γ⊢⟪a⟫ = Γ⊢⟪a⟫
    reflect (p ⊃ q) Γ⊢p⊃q Γ≼Γ′ Γ′⊩p =
      reflect q (app (⊢-≼ Γ≼Γ′ Γ⊢p⊃q) (reify p Γ′⊩p))
    reflect (p ∧ q) Γ⊢p∧q =
      reflect p (fst Γ⊢p∧q) , reflect q (snd Γ⊢p∧q)

  reflect-context : (Γ : List Formula) → Γ ⊪ Γ
  reflect-context [] = tt
  reflect-context (p ∷ Γ) =
    reflect p hyp , ⊪-≤ Γ (≼-cons ≼-refl) (reflect-context Γ)

  nbe : ∀ {Γ p} → Γ ⊢ p → Γ ⊢ p
  nbe {Γ} {p} Γ⊢p = reify p (soundness Γ⊢p (reflect-context Γ))
