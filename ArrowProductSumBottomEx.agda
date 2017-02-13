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

  ⊃-hyp : ∀ {p} → [] ⊢ p ⊃ p
  ⊃-hyp = lam hyp

  ⊃-wkn : ∀ {p q} → [] ⊢ p ⊃ q ⊃ p
  ⊃-wkn = lam (lam (wkn hyp)) 

  ⊃-cut : ∀ {p q r} → [] ⊢ (p ⊃ q ⊃ r) ⊃ (p ⊃ q) ⊃ p ⊃ r
  ⊃-cut = lam (lam (lam (app (app (wkn (wkn hyp)) hyp) (app (wkn hyp) hyp))))

  ∧-fst : ∀ {p q} → [] ⊢ p ∧ q ⊃ p
  ∧-fst = lam (fst hyp)

  ∧-snd : ∀ {p q} → [] ⊢ p ∧ q ⊃ q
  ∧-snd = lam (snd hyp)

  ∧-pair : ∀ {p q} → [] ⊢ p ⊃ q ⊃ p ∧ q
  ∧-pair = lam (lam (pair (wkn hyp) hyp))

  ∨-inl : ∀ {p q} → [] ⊢ p ⊃ p ∨ q
  ∨-inl = lam (inl hyp)

  ∨-inr : ∀ {p q} → [] ⊢ q ⊃ p ∨ q
  ∨-inr = lam (inr hyp)

  ∨-case : ∀ {p q r} → [] ⊢ (p ⊃ r) ⊃ (q ⊃ r) ⊃ p ∨ q ⊃ r
  ∨-case {p} {q} {r} = lam (lam (lam
    (case hyp (app (wkn (wkn (wkn hyp))) hyp) (app (wkn (wkn hyp)) hyp))))

  ⊃-mp : ∀ {p q} → [] ⊢ p ⊃ (p ⊃ q) ⊃ q
  ⊃-mp = lam (lam (app hyp (wkn hyp)))

  ⊃-trans : ∀ {p q r} → [] ⊢ p ⊃ (p ⊃ q) ⊃ (q ⊃ r) ⊃ r
  ⊃-trans = lam (lam (lam (app hyp (app (wkn hyp) (wkn (wkn hyp))))))

  ∧-comm : ∀ {p q} → [] ⊢ p ∧ q ⊃ q ∧ p
  ∧-comm = lam (pair (snd hyp) (fst hyp))

  ∧-assoc1 : ∀ {p q r} → [] ⊢ (p ∧ q) ∧ r ⊃ p ∧ (q ∧ r)
  ∧-assoc1 =
    lam (pair (fst (fst hyp)) (pair (snd (fst hyp)) (snd hyp)))

  ∧-assoc2 : ∀ {p q r} → [] ⊢ p ∧ (q ∧ r) ⊃ (p ∧ q) ∧ r
  ∧-assoc2 {p} {q} {r} =
    lam (pair (pair (fst hyp) (fst (snd hyp))) (snd (snd hyp)))

  ∨-comm : ∀ {p q} → [] ⊢ p ∨ q ⊃ q ∨ p
  ∨-comm = lam (case hyp (inr hyp) (inl hyp))

  ∨-assoc1 : ∀ {p q r} → [] ⊢ (p ∨ q) ∨ r ⊃ p ∨ (q ∨ r)
  ∨-assoc1 {p} {q} {r} =
    lam (case hyp (case hyp (inl hyp) (inr (inl hyp)))
                  (inr (inr hyp)))

  ∨-assoc2 : ∀ {p q r} → [] ⊢ p ∨ (q ∨ r) ⊃ (p ∨ q) ∨ r
  ∨-assoc2 {p} {q} {r} =
    lam (case hyp (inl (inl hyp))
                  (case hyp (inl (inr hyp)) (inr hyp)))

  ∧∨-distr1 : ∀ {p q r} → [] ⊢ p ∧ (q ∨ r) ⊃ (p ∧ q) ∨ (p ∧ r)
  ∧∨-distr1 =
    lam (case (snd hyp) (inl (pair (wkn (fst hyp)) hyp))
                        (inr (pair (wkn (fst hyp)) hyp)))

  ∧∨-distr2 : ∀ {p q r} → [] ⊢ (p ∧ q) ∨ (p ∧ r) ⊃ p ∧ (q ∨ r)
  ∧∨-distr2 =
    lam (case hyp (pair (fst hyp) (inl (snd hyp)))
                  (pair (fst hyp) (inr (snd hyp))))

  ∨∧-distr1 : ∀ {p q r} → [] ⊢ p ∨ (q ∧ r) ⊃ (p ∨ q) ∧ (p ∨ r)
  ∨∧-distr1 =
    lam (case hyp (pair (inl hyp) (inl hyp))
                  (pair (inr (fst hyp)) (inr (snd hyp))))

  ∨∧-distr2 : ∀ {p q r} → [] ⊢ (p ∨ q) ∧ (p ∨ r) ⊃ p ∨ (q ∧ r)
  ∨∧-distr2 =
    lam (case (fst hyp) (inl hyp)
              (case (snd (wkn hyp)) (inl hyp) (inr (pair (wkn hyp) hyp))))

  ∨⊃-distr1 : ∀ {p q r} → [] ⊢ (p ∨ q ⊃ r) ⊃ (p ⊃ r) ∧ (q ⊃ r)
  ∨⊃-distr1 =
    lam (pair (lam (app (wkn hyp) (inl hyp)))
              (lam (app (wkn hyp) (inr hyp))))

  ∨⊃-distr2 : ∀ {p q r} → [] ⊢ (p ⊃ r) ∧ (q ⊃ r) ⊃ (p ∨ q ⊃ r)
  ∨⊃-distr2 {p} {q} {r} =
    lam (lam (case hyp (app (wkn (wkn (fst hyp))) hyp)
                       (app (wkn (wkn (snd hyp))) hyp)))

  -- Negation

  -- ~ p ⊃ p ⊃ q
  ~-efq : ∀ {p q} → [] ⊢ (p ⊃ 𝟘) ⊃ p ⊃ q
  ~-efq = lam (lam (efq (app (wkn hyp) hyp)))

  -- (p ⊃ q) ⊃ (p ⊃ ~ q) ⊃ ~ p
  ~-abs : ∀ {p q} → [] ⊢ (p ⊃ q) ⊃ (p ⊃ q ⊃ 𝟘) ⊃ p ⊃ 𝟘
  ~-abs = lam (lam (lam (app (app (wkn hyp) hyp) (app (wkn (wkn hyp)) hyp))))

  -- (p ⊃ q) ⊃ (~ q ⊃ ~ p)
  ~⊃~ : ∀ {p q} → [] ⊢ (p ⊃ q) ⊃ (q ⊃ 𝟘) ⊃ p ⊃ 𝟘
  ~⊃~ = lam (lam (lam (app (wkn hyp) (app (wkn (wkn hyp)) hyp))))

  -- p ⊃ ~ ~ p
  ~~-intro : ∀ {p} → [] ⊢ p ⊃ (p ⊃ 𝟘) ⊃ 𝟘
  ~~-intro = lam (lam (app hyp (wkn hyp)))

  -- ~ ~ ~ p ⊂⊃ ~ p

  -- ~ ~ ~ p ⊃ ~ p
  ~~~-elim1 : ∀ {p} → [] ⊢ (((p ⊃ 𝟘) ⊃ 𝟘) ⊃ 𝟘) ⊃ p ⊃ 𝟘
  ~~~-elim1 = lam (lam (app (wkn hyp) (lam (app hyp (wkn hyp)))))

  -- ~ p ⊃ ~ ~ ~ p
  ~~~-elim2 : ∀ {p} → [] ⊢ (p ⊃ 𝟘) ⊃ ((p ⊃ 𝟘) ⊃ 𝟘) ⊃ 𝟘
  ~~~-elim2 = lam (lam (app hyp (wkn hyp)))

  -- De Morgan's law: ~ (p ∨ q) ⊂⊃ ~ p ∧ ~ q

  -- ~ (p ∨ q) ⊃ ~ p ∧ ~ q
  ~∨-distr1 : ∀ {p q} → [] ⊢ (p ∨ q ⊃ 𝟘) ⊃ (p ⊃ 𝟘) ∧ (q ⊃ 𝟘)
  ~∨-distr1 =
    lam (pair (lam (app (wkn hyp) (inl hyp)))
              (lam (app (wkn hyp) (inr hyp))))

  -- ~ p ∧ ~ q ⊃ ~ (p ∨ q)
  ~∨-distr2 : ∀ {p q} → [] ⊢ (p ⊃ 𝟘) ∧ (q ⊃ 𝟘) ⊃ p ∨ q ⊃ 𝟘
  ~∨-distr2 =
    lam (lam (case hyp (app (wkn (wkn (fst hyp))) hyp)
                       (app (wkn (wkn (snd hyp))) hyp)))

  -- p ∨ ~ p is not derivable, but
  -- ~ ~ (p ∨ ~ p)
  dn-tnd : ∀ {p} → [] ⊢ (p ∨ (p ⊃ 𝟘) ⊃ 𝟘) ⊃ 𝟘
  dn-tnd {p} =
    lam (app hyp (inr (lam (app (wkn hyp) (inl hyp)))))

  -- ~ ~ p ⊃ ~ ~ (p ⊃ q) ⊃ ~ ~ q
  dn-⊃-mp : ∀ {p q} → [] ⊢
    ((p ⊃ 𝟘) ⊃ 𝟘) ⊃ (((p ⊃ q) ⊃ 𝟘) ⊃ 𝟘) ⊃ (q ⊃ 𝟘) ⊃ 𝟘
  dn-⊃-mp =
    lam (lam (lam (app (wkn hyp)
                       (lam (app (wkn (wkn (wkn hyp)))
                                 (lam (app (wkn (wkn hyp))
                                      (app (wkn hyp) hyp))))))))

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
