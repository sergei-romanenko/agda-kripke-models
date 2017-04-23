module Classical.ArrowProductSumBottom-Ex where

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

open import Classical.ArrowProductSumBottom

module SampleClassicalProofs (Proposition : Set)  where

  open Logic Proposition

  -- ~ ~ p ⊃ p
  dneg : ∀ {p Γ} → Γ ⊢ ((p ⊃ 𝟘) ⊃ 𝟘) ⊃ p
  dneg = lam (abs (app (wkn hyp) hyp))

  -- ~ p ∨ p
  tnd : ∀ {p Γ} → Γ ⊢ (p ⊃ 𝟘) ∨ p
  tnd = app dneg (lam (app hyp (inl (lam (app (wkn hyp) (inr hyp))))))

  -- (~ p ⊃ q) ⊃ (p ⊃ q) ⊃ q
  split : ∀ {p Γ q} → (p ⊃ 𝟘) ∷ Γ ⊢ q → p ∷ Γ ⊢ q → Γ ⊢ q
  split = case tnd

  -- ~ (p ∧ q) ⊃ ~ p ∨ ~ q
  neg-and : ∀ {p q Γ} → Γ ⊢ (p ∧ q ⊃ 𝟘) ⊃ (p ⊃ 𝟘) ∨ (q ⊃ 𝟘)
  neg-and = lam (split (inl hyp) (split (inr hyp)
                (efq (app (wkn (wkn hyp)) (pair (wkn hyp) hyp)))))

  -- (p ⊃ q) ⊃ ~ p ∨ q
  imp-neg-or : ∀ {p q Γ} → Γ ⊢ (p ⊃ q) ⊃ (p ⊃ 𝟘) ∨ q
  imp-neg-or = lam (split (inl hyp) (inr (app (wkn hyp) hyp)))

  -- Peirce's law
  -- ((p ⊃ q) ⊃ p) ⊃ p

  peirce : ∀ {p} {q} {Γ} → Γ ⊢ ((p ⊃ q) ⊃ p) ⊃ p
  peirce = lam (split (app (wkn hyp) (lam (efq (app (wkn hyp) hyp)))) hyp)
