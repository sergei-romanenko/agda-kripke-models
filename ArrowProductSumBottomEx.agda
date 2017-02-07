module ArrowProductSumBottomEx where

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

open import ArrowProductSumBottom


module SampleProofs (Proposition : Set)  where

  open Logic Proposition

  p⊃p : ∀ {p} → [] ⊢ p ⊃ p
  p⊃p = lam hyp

  p-q-p : ∀ {p q} → [] ⊢ p ⊃ (q ⊃ p)
  p-q-p = lam (lam (wkn hyp)) 

  p-pq-q : ∀ {p q} → [] ⊢ p ⊃ ((p ⊃ q) ⊃ q)
  p-pq-q = lam (lam (app hyp (wkn hyp)))

  p∧q⊃q∧p : ∀ {p q} → [] ⊢ p ∧ q ⊃ q ∧ p
  p∧q⊃q∧p = lam (pair (snd hyp) (fst hyp))

  p∨q⊃q∨p : ∀ {p q} → [] ⊢ ((p ∨ q) ⊃ (q ∨ p))
  p∨q⊃q∨p = lam (case hyp (inr hyp) (inl hyp))

  ∧-assoc : ∀ {p q r} → [] ⊢ (p ∧ q) ∧ r ⊃ p ∧ (q ∧ r)
  ∧-assoc = lam (pair (fst (fst hyp)) (pair (snd (fst hyp)) (snd hyp)))

  [p∨q]⊃[p⊃r]⊃[q⊃r]⊃r : ∀ {p q r} → [] ⊢ (p ∨ q) ⊃ (p ⊃ r) ⊃ (q ⊃ r) ⊃ r
  [p∨q]⊃[p⊃r]⊃[q⊃r]⊃r =
    lam (lam (lam
      (case (wkn (wkn hyp)) (app (wkn (wkn hyp)) hyp) (app (wkn hyp) hyp))))

module Example1 where

  data Prop : Set where
    a : Prop

  data World : Set where
    w0 w1 : World

  data _⊫_ : World → Prop → Set where
    w1a : w1 ⊫ a

  data _≼_ : (w w′ : World) → Set where
    ≼00 : w0 ≼ w0
    ≼01 : w0 ≼ w1
    ≼11 : w1 ≼ w1

  ≼-refl : {w : World} → w ≼ w
  ≼-refl {w0} = ≼00
  ≼-refl {w1} = ≼11
 
  _⊙_ : {w w′ w′′ : World} → w ≼ w′ → w′ ≼ w′′ → w ≼ w′′
  ≼00 ⊙ ≼00 = ≼00
  ≼00 ⊙ ≼01 = ≼01
  ≼01 ⊙ ≼11 = ≼01
  ≼11 ⊙ ≼11 = ≼11

  ⊫-≼ : {a : Prop} {w w′ : World} → w ≼ w′ → w ⊫ a → w′ ⊫ a
  ⊫-≼ ≼11 w1a = w1a

  kripke : Kripke Prop
  kripke = record
    { K = World
    ; _≤_ = _≼_
    ; ≤-refl = ≼-refl
    ; _⊙_ = _⊙_
    ; _⊩ᵃ_ = _⊫_ ;
    ⊩ᵃ-≤ = ⊫-≼ }

  open Soundness Prop kripke

  a∨~a = ⟪ a ⟫ ∨ ~ ⟪ a ⟫

  ¬w0⊩a∨~a : ¬ (w0 ⊩ a∨~a)
  ¬w0⊩a∨~a (inj₁ ())
  ¬w0⊩a∨~a (inj₂ w0⊩⟪a⟫⊃𝟘) = w0⊩⟪a⟫⊃𝟘 ≼01 w1a

  ¬⊢a∨~a : ¬ ([] ⊢ a∨~a)
  ¬⊢a∨~a = ¬deducible w0 a∨~a ¬w0⊩a∨~a

  ~~a⊃a = ~ ~ ⟪ a ⟫ ⊃ ⟪ a ⟫

  ¬w0⊩~~a⊃a : ¬(w0 ⊩ ~~a⊃a)
  ¬w0⊩~~a⊃a w0⊩~~a⊃a
    with w0⊩~~a⊃a {w0} ≼00
      (λ where
         {w0} ≼00 f → f ≼01 w1a
         {w1} ≼01 f → f ≼11 w1a
      )
  ... | ()
