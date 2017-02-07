module ArrowProduct where

open import Data.List
open import Data.Unit
  hiding(_≤_)
open import Data.Empty
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.String using (String)

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

-- Syntax

module Logic (Proposition : Set) where

  infix 3 _⊢_
  infixr 4 _⊃_
  infixr 6 _∧_

  data Formula : Set where
    ⟪_⟫  : (a : Proposition) → Formula
    _⊃_ : (p q : Formula) → Formula
    _∧_ : (p q : Formula) → Formula

  data _⊢_ : List Formula → Formula → Set where
    hyp : ∀ {Γ p} → p ∷ Γ ⊢ p
    wkn : ∀ {Γ p q} → Γ ⊢ p → q ∷ Γ ⊢ p
    lam  : ∀ {Γ p q} → p ∷ Γ ⊢ q → Γ ⊢ p ⊃ q
    app  : ∀ {Γ p q} → Γ ⊢ p ⊃ q → Γ ⊢ p → Γ ⊢ q
    pair : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ q → Γ ⊢ p ∧ q
    fst : ∀ {Γ p q} → Γ ⊢ p ∧ q → Γ ⊢ p
    snd : ∀ {Γ p q} → Γ ⊢ p ∧ q → Γ ⊢ q

-- Worlds (Kripke structures)

record Kripke (Proposition : Set) : Set₁ where
  field
    K : Set
    _≤_ : K → K → Set
    ≤-refl : {w : K} → w ≤ w
    _⊙_ : {w w′ w′′ : K} → w ≤ w′ → w′ ≤ w′′ → w ≤ w′′
    _⊩ᵃ_ : K → Proposition → Set
    ⊩ᵃ-≤ : {a : Proposition} {w w′ : K} → w ≤ w′ → w ⊩ᵃ a → w′ ⊩ᵃ a

module Semantics (Proposition : Set) (kripke : Kripke Proposition) where

  open Logic Proposition
  open Kripke kripke

  infix 3 _⊩_ _⊪_

  _⊩_ : K → Formula → Set
  w ⊩ ⟪ a ⟫ = w ⊩ᵃ a
  w ⊩ p ⊃ q = {w′ : K} → w ≤ w′ → w′ ⊩ p → w′ ⊩ q
  w ⊩ p ∧ q = w ⊩ p × w ⊩ q

  _⊪_ : K → List Formula → Set
  w ⊪ [] = ⊤
  w ⊪ (p ∷ Γ) = w ⊩ p × w ⊪ Γ

  ⊩-≤ : ∀ p {w w′ : K} → w ≤ w′ → w ⊩ p → w′ ⊩ p
  ⊩-≤ ⟪ a ⟫ = ⊩ᵃ-≤
  ⊩-≤ (p ⊃ q) w≤w′ w⊩p⊃q w′≤w′′ =
    w⊩p⊃q (w≤w′ ⊙ w′≤w′′)
  ⊩-≤ (p ∧ q) w≤w′ =
    Prod.map (⊩-≤ p w≤w′) (⊩-≤ q w≤w′)

  ⊪-≤ : ∀ Γ {w w′ : K} → w ≤ w′ → w ⊪ Γ → w′ ⊪ Γ
  ⊪-≤ [] w≤w′ w⊪[] = tt
  ⊪-≤ (p ∷ Γ) w≤w′ =
    Prod.map (⊩-≤ p w≤w′) (⊪-≤ Γ w≤w′)

module Soundness (Proposition : Set) (kripke : Kripke Proposition) where

  open Logic Proposition
  open Kripke kripke
  open Semantics Proposition kripke
  
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

  -- Syntactic deducibility

  ¬deducible : ∀ w p → ¬ (w ⊩ p) → ¬ ([] ⊢ p)
  ¬deducible w p ¬w⊩p []⊢p =
    ¬w⊩p (soundness []⊢p tt)

module Completeness (Proposition : Set) where

  open Logic Proposition

  data _≼_ : (Γ Γ′ : List Formula) → Set where 
    ≼-refl : ∀ {Γ} → Γ ≼ Γ
    ≼-cons : ∀ {Γ Γ′ p} → Γ ≼ Γ′ → Γ ≼ (p ∷ Γ′)

  ≼-trans : ∀ {Γ Γ′ Γ′′} → Γ ≼ Γ′ → Γ′ ≼ Γ′′ → Γ ≼ Γ′′
  ≼-trans Γ≼Γ′ ≼-refl = Γ≼Γ′
  ≼-trans Γ≼Γ′ (≼-cons Γ′≼Γ′′) = ≼-cons (≼-trans Γ≼Γ′ Γ′≼Γ′′)

  ⊢-≼ : ∀ {p Γ Γ′} → Γ ≼ Γ′ → Γ ⊢ p → Γ′ ⊢ p
  ⊢-≼ ≼-refl Γ′⊢p = Γ′⊢p
  ⊢-≼ (≼-cons Γ≼Γ′) Γ⊢p = wkn (⊢-≼ Γ≼Γ′ Γ⊢p)

  uks : Kripke Proposition
  uks = record { K = List Formula;
                 _≤_ = _≼_;
                 ≤-refl = ≼-refl;
                 _⊙_ = ≼-trans;
                 _⊩ᵃ_ = λ Γ a → Γ ⊢ ⟪ a ⟫;
                 ⊩ᵃ-≤ = ⊢-≼ }

  open Kripke uks
  open Semantics Proposition uks
  open Soundness Proposition uks

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
