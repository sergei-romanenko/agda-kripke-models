module ArrowProductSumBottom where

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

----------
-- Syntax
----------

module Logic (Proposition : Set) where

  infix 3 _⊢_
  infixr 4 _⊃_
  infixr 6 _∧_
  infixr 5 _∨_
  infix 4 ~_

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
             Γ ⊢ (p ∨ q) → (p ∷ Γ) ⊢ r → (q ∷ Γ) ⊢ r → Γ ⊢ r
    efq : ∀ {Γ a} → 𝟘 ∷ Γ ⊢ ⟪ a ⟫

  𝟘∷⊢ : ∀ {Γ} p → 𝟘 ∷ Γ ⊢ p
  𝟘∷⊢ ⟪ a ⟫ =
    efq
  𝟘∷⊢ (p ⊃ q) =
    lam (wkn (𝟘∷⊢ q))
  𝟘∷⊢ (p ∧ q) =
    pair (𝟘∷⊢ p) (𝟘∷⊢ q)
  𝟘∷⊢ (p ∨ q) =
    inl (𝟘∷⊢ p)
  𝟘∷⊢ 𝟘 =
    hyp

  ⊢𝟘⊃ : ∀ {Γ} p → Γ ⊢ 𝟘 ⊃ p
  ⊢𝟘⊃ p = lam (𝟘∷⊢ p)

  efq′ : ∀ {Γ} p → Γ ⊢ 𝟘 → Γ ⊢ p
  efq′ p Γ⊢𝟘 = app (⊢𝟘⊃ p) Γ⊢𝟘

module SampleProofs (p q r : Logic.Formula String) where

  open Logic String

  p⊃p : [] ⊢ p ⊃ p
  p⊃p = lam hyp

  p-q-p : [] ⊢ p ⊃ (q ⊃ p)
  p-q-p = lam (lam (wkn hyp)) 

  p-pq-q : [] ⊢ p ⊃ ((p ⊃ q) ⊃ q)
  p-pq-q = lam (lam (app hyp (wkn hyp)))

  p∧q⊃q∧p : [] ⊢ p ∧ q ⊃ q ∧ p
  p∧q⊃q∧p = lam (pair (snd hyp) (fst hyp))

  p∨q⊃q∨p : [] ⊢ ((p ∨ q) ⊃ (q ∨ p))
  p∨q⊃q∨p = lam (case hyp (inr hyp) (inl hyp))

  ∧-assoc : [] ⊢ (p ∧ q) ∧ r ⊃ p ∧ (q ∧ r)
  ∧-assoc = lam (pair (fst (fst hyp)) (pair (snd (fst hyp)) (snd hyp)))

  [p∨q]⊃[p⊃r]⊃[q⊃r]⊃r : [] ⊢ (p ∨ q) ⊃ (p ⊃ r) ⊃ (q ⊃ r) ⊃ r
  [p∨q]⊃[p⊃r]⊃[q⊃r]⊃r =
    lam (lam (lam
      (case (wkn (wkn hyp)) (app (wkn (wkn hyp)) hyp) (app (wkn hyp) hyp))))

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
  w ⊩ p ∨ q = w ⊩ p ⊎ w ⊩ q
  w ⊩ 𝟘 = ⊥

  _⊪_ : K → List Formula → Set
  w ⊪ [] = ⊤
  w ⊪ (p ∷ Γ) = w ⊩ p × w ⊪ Γ

  ⊩-≤ : ∀ p {w w′ : K} → w ≤ w′ → w ⊩ p → w′ ⊩ p
  ⊩-≤ ⟪ a ⟫ = ⊩ᵃ-≤
  ⊩-≤ (p ⊃ q) w≤w′ w⊩p⊃q w′≤w′′ =
    w⊩p⊃q (w≤w′ ⊙ w′≤w′′)
  ⊩-≤ (p ∧ q) w≤w′ =
    Prod.map (⊩-≤ p w≤w′) (⊩-≤ q w≤w′)
  ⊩-≤ (p ∨ q) w≤w′ =
    Sum.map (⊩-≤ p w≤w′) (⊩-≤ q w≤w′)
  ⊩-≤ 𝟘 w≤w′ ()

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
  soundness (inl Γ⊢p) w⊪Γ =
    inj₁ (soundness Γ⊢p w⊪Γ)
  soundness (inr Γ⊢p) w⊪Γ =
    inj₂ (soundness Γ⊢p w⊪Γ)
  soundness {Γ} {r} (case Γ⊢p∨q p∷Γ⊢r q∷Γ⊢r) w⊪Γ =
    [ (λ w⊩p → soundness p∷Γ⊢r (w⊩p , w⊪Γ)) ,
      (λ w⊩q → soundness q∷Γ⊢r (w⊩q , w⊪Γ)) ]′
      (soundness Γ⊢p∨q w⊪Γ)
  soundness efq (() , w⊪Γ)
