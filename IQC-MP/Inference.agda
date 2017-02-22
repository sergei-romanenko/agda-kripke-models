module IQC-MP.Inference where


open import Data.List
open import Data.List.Any as Any
  using (Any; here; there; module Membership-≡)
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
open Membership-≡ using (_∈_)

-- Syntax

module Logic (Proposition : Set) where

  infix 3 _⊢_!_
  infixr 4 _⊃_
  infixr 6 _∧_
  infixr 5 _∨_
  infix 7 ~_

  data Formula : Set where
    ⟪_⟫  : (a : Proposition) → Formula
    _⊃_ : (p q : Formula) → Formula
    _∧_ : (p q : Formula) → Formula
    _∨_ : (p q : Formula) → Formula
    𝟙 : Formula
    𝟘 : Formula

  ⊃-free : Formula → Set
  ⊃-free ⟪ a ⟫ = ⊤
  ⊃-free (p ⊃ q) = ⊥
  ⊃-free (p ∧ q) = ⊃-free p × ⊃-free q
  ⊃-free (p ∨ q) = ⊃-free p × ⊃-free q
  ⊃-free 𝟙 = ⊤
  ⊃-free 𝟘 = ⊤

  ~_ : ∀ (p : Formula) → Formula
  ~ p = p ⊃ 𝟘

  Ctx : Set
  Ctx = List Formula

  data _⊢_!_ : Ctx → Ctx → Formula → Set where
    hyp : ∀ {Γ Δ p} → p ∷ Γ ⊢ Δ ! p
    wkn : ∀ {Γ Δ p q} → Γ ⊢ Δ ! p → q ∷ Γ ⊢ Δ ! p
    lam  : ∀ {Γ Δ p q} → p ∷ Γ ⊢ Δ ! q → Γ ⊢ Δ ! p ⊃ q
    app  : ∀ {Γ Δ p q} → Γ ⊢ Δ ! p ⊃ q → Γ ⊢ Δ ! p → Γ ⊢ Δ ! q
    pair : ∀ {Γ Δ p q} → Γ ⊢ Δ ! p → Γ ⊢ Δ ! q → Γ ⊢ Δ ! p ∧ q
    fst : ∀ {Γ Δ p q} → Γ ⊢ Δ ! p ∧ q → Γ ⊢ Δ ! p
    snd : ∀ {Γ Δ p q} → Γ ⊢ Δ ! p ∧ q → Γ ⊢ Δ ! q
    inl : ∀ {Γ Δ p q} → Γ ⊢ Δ ! p → Γ ⊢ Δ ! p ∨ q
    inr : ∀ {Γ Δ p q} → Γ ⊢ Δ ! q → Γ ⊢ Δ ! p ∨ q
    case : ∀ {Γ Δ p q r} → Γ ⊢ Δ ! (p ∨ q) →
             (p ∷ Γ) ⊢ Δ ! r → (q ∷ Γ) ⊢ Δ ! r → Γ ⊢ Δ ! r
    true : ∀ {Γ Δ} → Γ ⊢ Δ ! 𝟙
    abort : ∀ {Γ Δ} → Γ ⊢ Δ ! 𝟘 → ∀ a → Γ ⊢ Δ ! ⟪ a ⟫
    catch : ∀ {Γ Δ t} → ⊃-free t →
              Γ ⊢ t ∷ Δ ! t → Γ ⊢ Δ ! t
    throw : ∀ {Γ Δ t p} → ⊃-free t → t ∈ Δ →
              Γ ⊢ Δ ! t → Γ ⊢ Δ ! p

  efq : ∀ {Γ Δ p} → Γ ⊢ Δ ! 𝟘 → Γ ⊢ Δ ! p
  efq {p = ⟪ a ⟫} Γ⊢Δ!𝟘 =
    abort Γ⊢Δ!𝟘 a
  efq {p = p ⊃ q} Γ⊢Δ!𝟘 =
    lam (wkn (efq Γ⊢Δ!𝟘))
  efq {p = p ∧ q} Γ⊢Δ!𝟘 =
    pair (efq Γ⊢Δ!𝟘) (efq Γ⊢Δ!𝟘)
  efq {p = p ∨ q} Γ⊢Δ!𝟘 =
    inl (efq Γ⊢Δ!𝟘)
  efq {p = 𝟙} Γ⊢Δ!𝟘 =
    true
  efq {p = 𝟘} Γ⊢Δ!𝟘 =
    Γ⊢Δ!𝟘

  markov-principle : ∀ {Γ Δ} t → ⊃-free t → Γ ⊢ Δ ! ~ ~ t ⊃ t
  markov-principle t ⊃f =
    lam (catch ⊃f (efq (app hyp (lam (throw ⊃f (here refl) hyp)))))
