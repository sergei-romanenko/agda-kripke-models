module ArrowProductSumNBE-CBN-Ex where

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

open import ArrowProductSumNBE-CBN

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

  ∨-inl : ∀ {p q} → [] ⊢ p ⊃ p ∨ q
  ∨-inl = lam (inl hyp)

  ∨-inr : ∀ {p q} → [] ⊢ q ⊃ p ∨ q
  ∨-inr = lam (inr hyp)

  ∨-case : ∀ {p q r} → [] ⊢ (p ⊃ r) ⊃ (q ⊃ r) ⊃ p ∨ q ⊃ r
  ∨-case {p} {q} {r} = lam (lam (lam
    (case hyp (app (wkn (wkn (wkn hyp))) hyp) (app (wkn (wkn hyp)) hyp))))

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

  ⊢p∧q₁ : ∀ {p q r} → r ∷ p ∷ q ∷ [] ⊢ p ∧ q
  ⊢p∧q₁ = pair (wkn hyp) (wkn (wkn hyp))

  ⊢p∧q₂ : ∀ {p q r} → r ∷ p ∷ q ∷ [] ⊢ p ∧ q
  ⊢p∧q₂ = wkn (pair hyp (wkn hyp))


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


module SampleProofsR (Atomic : Set) where

  open Logic Atomic

  snd-wkn : ∀ {p q r} → p ∷ (q ∧ r) ∷ [] ⊢ʳ r
  snd-wkn = ne (snd (wkn (ne hyp)))

  snd-wkn′ : ∀ {p q r} → p ∷ (q ∧ r) ∷ [] ⊢ʳ r
  snd-wkn′ = ne (wkn (ne (snd hyp)))

  ⊃-hyp : ∀ {p} → [] ⊢ʳ p ⊃ p
  ⊃-hyp = lam (ne hyp)

  ⊃-wkn : ∀ {p q} → [] ⊢ʳ p ⊃ q ⊃ p
  ⊃-wkn = lam (lam (ne (wkn (ne hyp))))

  ⊃-mp : ∀ {p q} → [] ⊢ʳ p ⊃ (p ⊃ q) ⊃ q
  ⊃-mp = lam (lam (ne (app hyp (ne (wkn (ne hyp))))))

  ⊃-trans : ∀ {p q r} → [] ⊢ʳ p ⊃ (p ⊃ q) ⊃ (q ⊃ r) ⊃ r
  ⊃-trans =
    lam (lam (lam (ne (app hyp
                           (ne (app (wkn (ne hyp))
                                    (ne (wkn (ne (wkn (ne hyp)))))))))))

  ⊃-cut : ∀ {p q r} → [] ⊢ʳ (p ⊃ q ⊃ r) ⊃ (p ⊃ q) ⊃ p ⊃ r
  ⊃-cut =
    lam (lam (lam (ne (app (app (wkn (ne (wkn (ne hyp)))) (ne hyp))
                           (ne (app (wkn (ne hyp)) (ne hyp)))))))

  ∧-comm : ∀ {p q} → [] ⊢ʳ p ∧ q ⊃ q ∧ p
  ∧-comm = lam (pair (ne (snd hyp)) (ne (fst hyp)))

  ∧-assoc : ∀ {p q r} → [] ⊢ʳ (p ∧ q) ∧ r ⊃ p ∧ (q ∧ r)
  ∧-assoc = lam (pair (ne (fst (fst hyp)))
                      (pair (ne (snd (fst hyp))) (ne (snd hyp))))
