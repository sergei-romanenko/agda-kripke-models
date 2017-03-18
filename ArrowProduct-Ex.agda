module ArrowProduct-Ex where

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

module SampleProofs (Atomic : Set) where

  open Logic Atomic

  snd-wkn : ∀ {p q r} → p ∷ (q ∧ r) ∷ [] ⊢ r
  snd-wkn = snd (wkn hyp)

  snd-wkn′ : ∀ {p q r} → p ∷ (q ∧ r) ∷ [] ⊢ r
  snd-wkn′ = wkn (snd hyp)

  ⊃-hyp : ∀ {p} → [] ⊢ p ⊃ p
  ⊃-hyp = lam hyp

  ⊃-wkn : ∀ {p q} → [] ⊢ p ⊃ q ⊃ p
  ⊃-wkn = lam (lam (wkn hyp)) 

  ⊃-mp : ∀ {p q} → [] ⊢ p ⊃ (p ⊃ q) ⊃ q
  ⊃-mp = lam (lam (app hyp (wkn hyp)))

  ⊃-trans : ∀ {p q r} → [] ⊢ p ⊃ (p ⊃ q) ⊃ (q ⊃ r) ⊃ r
  ⊃-trans = lam (lam (lam (app hyp (app (wkn hyp) (wkn (wkn hyp))))))

  ⊃-cut : ∀ {p q r} → [] ⊢ (p ⊃ q ⊃ r) ⊃ (p ⊃ q) ⊃ p ⊃ r
  ⊃-cut = lam (lam (lam (app (app (wkn (wkn hyp)) hyp) (app (wkn hyp) hyp))))

  ∧-fst : ∀ {p q} → [] ⊢ p ∧ q ⊃ p
  ∧-fst = lam (fst hyp)

  ∧-snd : ∀ {p q} → [] ⊢ p ∧ q ⊃ q
  ∧-snd = lam (snd hyp)

  ∧-pair : ∀ {p q} → [] ⊢ p ⊃ q ⊃ p ∧ q
  ∧-pair = lam (lam (pair (wkn hyp) hyp))

  ∧-comm : ∀ {p q} → [] ⊢ p ∧ q ⊃ q ∧ p
  ∧-comm = lam (pair (snd hyp) (fst hyp))

  ∧-assoc1 : ∀ {p q r} → [] ⊢ (p ∧ q) ∧ r ⊃ p ∧ (q ∧ r)
  ∧-assoc1 =
    lam (pair (fst (fst hyp)) (pair (snd (fst hyp)) (snd hyp)))

  ∧-assoc2 : ∀ {p q r} → [] ⊢ p ∧ (q ∧ r) ⊃ (p ∧ q) ∧ r
  ∧-assoc2 {p} {q} {r} =
    lam (pair (pair (fst hyp) (fst (snd hyp))) (snd (snd hyp)))

  ⊢p∧q₁ : ∀ {p q r} → r ∷ p ∷ q ∷ [] ⊢ p ∧ q
  ⊢p∧q₁ = pair (wkn hyp) (wkn (wkn hyp))

  ⊢p∧q₂ : ∀ {p q r} → r ∷ p ∷ q ∷ [] ⊢ p ∧ q
  ⊢p∧q₂ = wkn (pair hyp (wkn hyp))


module NBE-Samples (Atomic : Set) (a b c : Atomic) where

  open Logic Atomic
  open Completeness Atomic

  id-id : [] ⊢ ⟪ a ⟫ ⊃ ⟪ a ⟫
  id-id = app (lam hyp) (lam hyp)

  nbe-id-id : nbe id-id ≡ lam hyp
  nbe-id-id = refl

  fst-pair : [] ⊢ ⟪ a ⟫ ⊃ ⟪ b ⟫ ⊃ ⟪ a ⟫
  fst-pair = lam (lam (fst (pair (wkn hyp) hyp)))

  nbe-fst-pair : nbe fst-pair ≡ lam (lam (wkn hyp))
  nbe-fst-pair = refl

  ⊢a∧b : ⟪ c ⟫ ∷ ⟪ a ⟫ ∷ ⟪ b ⟫ ∷ [] ⊢ ⟪ a ⟫ ∧ ⟪ b ⟫
  ⊢a∧b = wkn (pair hyp (wkn hyp))

  nbe-⊢a∧b : nbe ⊢a∧b ≡ pair (wkn hyp) (wkn (wkn hyp))
  nbe-⊢a∧b = refl
