module Classical.ArrowProductSumBottom where

open import Data.List
open import Data.Unit
  hiding(_≤_)
open import Data.Empty
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.String using (String)

open import Function

open import Relation.Nullary
open import Relation.Nullary.Product
open import Relation.Nullary.Sum
open import Relation.Nullary.Implication
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

-- Syntax

module Logic (Proposition : Set) where

  infix 3 _⊢_
  infixr 4 _⊃_
  infixr 6 _∧_
  infixr 5 _∨_
  infix 7 ~_

  data Formula : Set where
    ⟪_⟫  : (a : Proposition) → Formula
    _⊃_ : (p q : Formula) → Formula
    _∧_ : (p q : Formula) → Formula
    _∨_ : (p q : Formula) → Formula
    𝟘 : Formula

  ~_ : ∀ (p : Formula) → Formula
  ~ p = p ⊃ 𝟘

  Ctx : Set
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
    case : ∀ {Γ p q r} →
             Γ ⊢ p ∨ q → p ∷ Γ ⊢ r → q ∷ Γ ⊢ r → Γ ⊢ r
    abort : ∀ {Γ a} → Γ ⊢ 𝟘 → Γ ⊢ ⟪ a ⟫
    --  The classical negation rule!!!
    abs : ∀ {Γ p} → (p ⊃ 𝟘) ∷ Γ ⊢ 𝟘 → Γ ⊢ p

  efq : ∀ {p Γ} → Γ ⊢ 𝟘 → Γ ⊢ p
  efq {⟪ a ⟫} Γ⊢𝟘 =
    abort Γ⊢𝟘
  efq {p ⊃ q} Γ⊢𝟘 =
    lam (wkn (efq Γ⊢𝟘))
  efq {p ∧ q} Γ⊢𝟘 =
    pair (efq Γ⊢𝟘) (efq Γ⊢𝟘)
  efq {p ∨ q} Γ⊢𝟘 =
    inl (efq Γ⊢𝟘)
  efq {𝟘} Γ⊢𝟘 = Γ⊢𝟘

-- Worlds (interpretations)

record Struct (Proposition : Set) : Set₁ where
  field
    World : Set
    _⊩ᵃ_ : World → Proposition → Set
    _⊩ᵃ?_ : ∀ w a → Dec (w ⊩ᵃ a)

module Semantics (Proposition : Set) (struct : Struct Proposition) where

  open Logic Proposition
  open Struct struct

  infix 3 _⊩_ _⊪_

  _⊩_ : World → Formula → Set
  w ⊩ ⟪ a ⟫ = w ⊩ᵃ a
  w ⊩ p ⊃ q = w ⊩ p → w ⊩ q
  w ⊩ p ∧ q = w ⊩ p × w ⊩ q
  w ⊩ p ∨ q = w ⊩ p ⊎ w ⊩ q
  w ⊩ 𝟘 = ⊥

  _⊪_ : World → List Formula → Set
  w ⊪ [] = ⊤
  w ⊪ (p ∷ Γ) = w ⊩ p × w ⊪ Γ

  _⊩?_ : ∀ w p → Dec (w ⊩ p)
  w ⊩? ⟪ a ⟫ = w ⊩ᵃ? a
  w ⊩? (p ⊃ q) = (w ⊩? p) →-dec (w ⊩? q)
  w ⊩? (p ∧ q) = (w ⊩? p) ×-dec (w ⊩? q)
  w ⊩? (p ∨ q) = (w ⊩? p) ⊎-dec (w ⊩? q)
  w ⊩? 𝟘 = no id

module Soundness (Proposition : Set) (struct : Struct Proposition) where

  open Logic Proposition public
  open Struct struct public
  open Semantics Proposition struct public

  soundness : ∀ {Γ p} → Γ ⊢ p → ∀ {w} → w ⊪ Γ → w ⊩ p
  soundness hyp w⊪p∷Γ =
    proj₁ w⊪p∷Γ
  soundness (wkn Γ⊢p) w⊪p∷Γ =
    soundness Γ⊢p (proj₂ w⊪p∷Γ)
  soundness (lam Γ⊢p) w⊪Γ w⊩p =
    soundness Γ⊢p (w⊩p , w⊪Γ)
  soundness (app Γ⊢p⊃q Γ⊢p) w⊪Γ =
    soundness Γ⊢p⊃q w⊪Γ (soundness Γ⊢p w⊪Γ)
  soundness (pair Γ⊢p Γ⊢q) w⊪Γ =
    soundness Γ⊢p w⊪Γ , soundness Γ⊢q w⊪Γ
  soundness (fst Γ⊢p∧q) w⊪Γ =
    proj₁ (soundness Γ⊢p∧q w⊪Γ)
  soundness (snd Γ⊢p∧q) w⊪Γ =
    proj₂ (soundness Γ⊢p∧q w⊪Γ)
  soundness (inl Γ⊢p) w⊪Γ =
    inj₁ (soundness Γ⊢p w⊪Γ)
  soundness (inr Γ⊢p) w⊪Γ =
    inj₂ (soundness Γ⊢p w⊪Γ)
  soundness (case Γ⊢p∨q p∷Γ⊢r q∷Γ⊢r) w⊪Γ
    with soundness Γ⊢p∨q w⊪Γ
  ... | inj₁ w⊩p = soundness p∷Γ⊢r (w⊩p , w⊪Γ)
  ... | inj₂ w⊩q = soundness q∷Γ⊢r (w⊩q , w⊪Γ)
  soundness (abort Γ⊢𝟘) w⊪Γ =
    ⊥-elim (soundness Γ⊢𝟘 w⊪Γ)
  soundness (abs {p = p} p⊃𝟘∷Γ⊢𝟘) {w} w⊪Γ with w ⊩? p
  ... | yes w⊩p = w⊩p
  ... | no ¬w⊩p = ⊥-elim (soundness p⊃𝟘∷Γ⊢𝟘 (¬w⊩p , w⊪Γ))

  -- Syntactic deducibility

  ¬deducible : ∀ w p → ¬ (w ⊩ p) → ¬ ([] ⊢ p)
  ¬deducible w p ¬w⊩p []⊢p =
    ¬w⊩p (soundness []⊢p tt)
