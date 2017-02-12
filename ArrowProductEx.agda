module ArrowProductEx where

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

open import ArrowProduct

module SampleProofs (Proposition : Set) where

  open Logic Proposition

  snd-wkn : ∀ {p q r} → (p ∷ (q ∧ r) ∷ []) ⊢ r
  snd-wkn = snd (wkn hyp)

  snd-wkn′ : ∀ {p q r} → (p ∷ (q ∧ r) ∷ []) ⊢ r
  snd-wkn′ = wkn (snd hyp)

  p⊃p : ∀ {p} → [] ⊢ (p ⊃ p)
  p⊃p = lam hyp

  p-q-p : ∀ {p q} → [] ⊢ (p ⊃ (q ⊃ p))
  p-q-p = lam (lam (wkn hyp)) 

  p-pq-q : ∀ {p q} → [] ⊢ (p ⊃ ((p ⊃ q) ⊃ q))
  p-pq-q = lam (lam (app hyp (wkn hyp)))

  p∧q⊃q∧p : ∀ {p q} → [] ⊢ ((p ∧ q) ⊃ (q ∧ p))
  p∧q⊃q∧p = lam (pair (snd hyp) (fst hyp))

  ∧-assoc : ∀ {p q r} → [] ⊢ (((p ∧ q) ∧ r) ⊃ (p ∧ (q ∧ r)))
  ∧-assoc = lam (pair (fst (fst hyp)) (pair (snd (fst hyp)) (snd hyp)))

  ⊢p∧q₁ : ∀ {p q r} → (r ∷ p ∷ q ∷ []) ⊢ (p ∧ q)
  ⊢p∧q₁ = pair (wkn hyp) (wkn (wkn hyp))

  ⊢p∧q₂ : ∀ {p q r} → (r ∷ p ∷ q ∷ []) ⊢ (p ∧ q)
  ⊢p∧q₂ = wkn (pair hyp (wkn hyp))


module NBE-Samples (Proposition : Set) (a b c : Proposition) where

  open Logic Proposition
  open Completeness Proposition

  id-id : [] ⊢ (⟪ a ⟫ ⊃ ⟪ a ⟫)
  id-id = app (lam hyp) (lam hyp)

  nbe-id-id : nbe id-id ≡ lam hyp
  nbe-id-id = refl

  fst-pair : [] ⊢ (⟪ a ⟫ ⊃ (⟪ b ⟫ ⊃ ⟪ a ⟫))
  fst-pair = lam (lam (fst (pair (wkn hyp) hyp)))

  nbe-fst-pair : nbe fst-pair ≡ lam (lam (wkn hyp))
  nbe-fst-pair = refl

  ⊢a∧b : (⟪ c ⟫ ∷ ⟪ a ⟫ ∷ ⟪ b ⟫ ∷ []) ⊢ (⟪ a ⟫ ∧ ⟪ b ⟫)
  ⊢a∧b = wkn (pair hyp (wkn hyp))

  nbe-⊢a∧b : nbe ⊢a∧b ≡ pair (wkn hyp) (wkn (wkn hyp))
  nbe-⊢a∧b = refl