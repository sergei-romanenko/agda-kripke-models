module ArrowProductNBE where

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

-- Syntax

module Logic (Atomic : Set) where

  infix 3 _⊢_ _⊢ʳ_ _⊢ᵉ_
  infixr 4 _⊃_
  infixr 6 _∧_

  data Formula : Set where
    ⟪_⟫  : (a : Atomic) → Formula
    _⊃_ : (p q : Formula) → Formula
    _∧_ : (p q : Formula) → Formula

  Ctx = List Formula

  -- Source language: natural deduction

  data _⊢_ : Ctx → Formula → Set where
    hyp : ∀ {Γ p} → p ∷ Γ ⊢ p
    wkn : ∀ {Γ p q} → Γ ⊢ p → q ∷ Γ ⊢ p
    lam : ∀ {Γ p q} → p ∷ Γ ⊢ q → Γ ⊢ p ⊃ q
    app : ∀ {Γ p q} → Γ ⊢ p ⊃ q → Γ ⊢ p → Γ ⊢ q
    pair : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ q → Γ ⊢ p ∧ q
    fst : ∀ {Γ p q} → Γ ⊢ p ∧ q → Γ ⊢ p
    snd : ∀ {Γ p q} → Γ ⊢ p ∧ q → Γ ⊢ q

  -- Target language: natural deduction allowing only beta-normal forms

  mutual

    data _⊢ʳ_ : Ctx → Formula → Set where
      ne : ∀ {Γ p} → Γ ⊢ᵉ p → Γ ⊢ʳ p
      lam : ∀ {Γ p q} → p ∷ Γ ⊢ʳ q → Γ ⊢ʳ p ⊃ q
      pair : ∀ {Γ p q} → Γ ⊢ʳ p → Γ ⊢ʳ q → Γ ⊢ʳ p ∧ q

    data _⊢ᵉ_ : Ctx → Formula → Set where
      hyp : ∀ {Γ p} → p ∷ Γ ⊢ᵉ p
      wkn : ∀ {Γ p q} → Γ ⊢ʳ p → q ∷ Γ ⊢ᵉ p
      app : ∀ {Γ p q} → Γ ⊢ᵉ p ⊃ q → Γ ⊢ʳ p → Γ ⊢ᵉ q
      fst : ∀ {Γ p q} → Γ ⊢ᵉ p ∧ q → Γ ⊢ᵉ p
      snd : ∀ {Γ p q} → Γ ⊢ᵉ p ∧ q → Γ ⊢ᵉ q

-- Worlds (Kripke structures)

record Kripke (Proposition : Set) : Set₁ where
  field
    World : Set
    _≤_ : World → World → Set
    ε : ∀ {w} → w ≤ w
    _⊙_ : ∀ {w w′ w′′} → w ≤ w′ → w′ ≤ w′′ → w ≤ w′′
    _⊩ᵃ_ : World → Proposition → Set
    ⊩ᵃ≤ : ∀ {a w w′} → w ≤ w′ → w ⊩ᵃ a → w′ ⊩ᵃ a

module Semantics (Proposition : Set) (kripke : Kripke Proposition) where

  open Logic Proposition
  open Kripke kripke

  infix 3 _⊩_ _⊪_

  _⊩_ : World → Formula → Set
  w ⊩ ⟪ a ⟫ = w ⊩ᵃ a
  w ⊩ p ⊃ q = ∀ {w′} → w ≤ w′ → w′ ⊩ p → w′ ⊩ q
  w ⊩ p ∧ q = w ⊩ p × w ⊩ q

  _⊪_ : World → Ctx → Set
  w ⊪ [] = ⊤
  w ⊪ (p ∷ Γ) = w ⊩ p × w ⊪ Γ

  ⊩≤ : ∀ p {w w′} → w ≤ w′ → w ⊩ p → w′ ⊩ p
  ⊩≤ ⟪ a ⟫ = ⊩ᵃ≤
  ⊩≤ (p ⊃ q) ≤′ w⊩p⊃q ≤′′ =
    w⊩p⊃q (≤′ ⊙ ≤′′)
  ⊩≤ (p ∧ q) ≤′ =
    Prod.map (⊩≤ p ≤′) (⊩≤ q ≤′)

  ⊪≤ : ∀ Γ {w w′} → w ≤ w′ → w ⊪ Γ → w′ ⊪ Γ
  ⊪≤ [] ≤′ w⊪[] = tt
  ⊪≤ (p ∷ Γ) ≤′ =
    Prod.map (⊩≤ p ≤′) (⊪≤ Γ ≤′)

module Soundness (Proposition : Set) (kripke : Kripke Proposition) where

  open Logic Proposition
  open Kripke kripke
  open Semantics Proposition kripke

  soundness : ∀ {Γ p} → Γ ⊢ p → ∀ {w} → w ⊪ Γ → w ⊩ p
  soundness hyp w⊪p∷Γ =
    proj₁ w⊪p∷Γ
  soundness (wkn Γ⊢p) w⊪p∷Γ =
    soundness Γ⊢p (proj₂ w⊪p∷Γ)
  soundness {Γ} (lam Γ⊢p) w⊪Γ ≤′ w′⊩p =
    soundness Γ⊢p (w′⊩p , ⊪≤ Γ ≤′ w⊪Γ)
  soundness (app Γ⊢p⊃q Γ⊢p) w⊪Γ =
    soundness Γ⊢p⊃q w⊪Γ ε (soundness Γ⊢p w⊪Γ)
  soundness (pair Γ⊢p Γ⊢q) w⊪Γ =
    soundness Γ⊢p w⊪Γ , soundness Γ⊢q w⊪Γ
  soundness (fst Γ⊢p∧q) w⊪Γ =
    proj₁ (soundness Γ⊢p∧q w⊪Γ)
  soundness (snd Γ⊢p∧q) w⊪Γ =
    proj₂ (soundness Γ⊢p∧q w⊪Γ)

module Completeness (Atomic : Set) where

  open Logic Atomic

  data _≼_ : (Γ Γ′ : Ctx) → Set where 
    ≼-refl : ∀ {Γ} → Γ ≼ Γ
    ≼-cons : ∀ {Γ Γ′ p} → Γ ≼ Γ′ → Γ ≼ (p ∷ Γ′)

  δ : ∀ {Γ p} → Γ ≼ (p ∷ Γ)
  δ = ≼-cons ≼-refl

  ≼-trans : ∀ {Γ Γ′ Γ′′} → Γ ≼ Γ′ → Γ′ ≼ Γ′′ → Γ ≼ Γ′′
  ≼-trans ≼′ ≼-refl = ≼′
  ≼-trans ≼′ (≼-cons ≼′′) = ≼-cons (≼-trans ≼′ ≼′′)

  ⊢ᵉ≼ : ∀ {p Γ Γ′} → Γ ≼ Γ′ → Γ ⊢ᵉ p → Γ′ ⊢ᵉ p
  ⊢ᵉ≼ ≼-refl Γ′⊢ᵉp = Γ′⊢ᵉp
  ⊢ᵉ≼ (≼-cons ≼′) Γ⊢ᵉp = wkn (ne (⊢ᵉ≼ ≼′ Γ⊢ᵉp))

  ⊢ʳ≼ : ∀ {p Γ Γ′} → Γ ≼ Γ′ → Γ ⊢ʳ p → Γ′ ⊢ʳ p
  ⊢ʳ≼ ≼-refl Γ⊢ʳp = Γ⊢ʳp
  ⊢ʳ≼ (≼-cons ≼′) Γ⊢ʳp = ne (wkn (⊢ʳ≼ ≼′ Γ⊢ʳp))

  uks : Kripke Atomic
  uks = record
    { World = Ctx
    ; _≤_ = _≼_
    ; ε = ≼-refl
    ; _⊙_ = ≼-trans
    ; _⊩ᵃ_ = λ Γ a → Γ ⊢ʳ ⟪ a ⟫
    ; ⊩ᵃ≤ = ⊢ʳ≼
    }

  open Kripke uks
  open Semantics Atomic uks
  open Soundness Atomic uks

  mutual
    reify : ∀ {p Γ} → Γ ⊩ p → Γ ⊢ʳ p
    reify {⟪ a ⟫} Γ⊩⟪a⟫ = Γ⊩⟪a⟫
    reify {p ⊃ q} Γ⊩p⊃q =
      lam (reify (Γ⊩p⊃q δ (reflect {p} hyp)))
    reify {p ∧ q} Γ⊩p∧q =
      pair (reify (proj₁ Γ⊩p∧q)) (reify (proj₂ Γ⊩p∧q))

    reflect : ∀ {p Γ} → Γ ⊢ᵉ p → Γ ⊩ p
    reflect {⟪ a ⟫} Γ⊢ᵉ⟪a⟫ = ne Γ⊢ᵉ⟪a⟫
    reflect {p ⊃ q} Γ⊢ᵉp⊃q ≼′ Γ′⊩p =
      reflect (app Γ′⊢ᵉp⊃q (reify Γ′⊩p))
      where Γ′⊢ᵉp⊃q = ⊢ᵉ≼ ≼′ Γ⊢ᵉp⊃q
    reflect {p ∧ q} Γ⊢ᵉp∧q =
      reflect (fst Γ⊢ᵉp∧q) , reflect (snd Γ⊢ᵉp∧q)

    reflect-context : (Γ : Ctx) → Γ ⊪ Γ
    reflect-context [] = tt
    reflect-context (p ∷ Γ) =
      reflect {p} hyp , ⊪≤ Γ δ (reflect-context Γ)

  nbe : ∀ {Γ p} → Γ ⊢ p → Γ ⊢ʳ p
  nbe {Γ} Γ⊢p = reify (soundness Γ⊢p (reflect-context Γ))
