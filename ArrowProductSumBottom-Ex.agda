module ArrowProductSumBottom-Ex where

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

module SampleProofs (Atomic : Set)  where

  open Logic Atomic

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
  ∨-case = lam (lam (lam
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

  ∧le : ∀ {p q r Γ} → (p ∧ q) ∷ Γ ⊢ r → p ∷ q ∷ Γ ⊢ r
  ∧le p∧q∷Γ⊢r =
    app (wkn (app (wkn (app
      (lam (lam (lam (app (wkn (wkn hyp)) (pair hyp (wkn hyp))))))
      (lam p∧q∷Γ⊢r))) hyp)) hyp

  ∧-cut : ∀ {p q r Γ} → (r ∧ p) ∷ Γ ⊢ q → p ∷ Γ ⊢ r ∨ q → p ∷ Γ ⊢ q
  ∧-cut rp⊢q p⊢r∨q =
    case p⊢r∨q (∧le rp⊢q) hyp

  -- Negation

  -- ~ p ⊃ p ⊃ q
  contradict : ∀ {p q} → [] ⊢ (p ⊃ 𝟘) ⊃ p ⊃ q
  contradict = lam (lam (efq (app (wkn hyp) hyp)))

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

  -- ~ p ∨ p is not derivable, but
  -- ~ ~ (~ p ∨ p)

  ~~tnd : ∀ {p} → [] ⊢ ((p ⊃ 𝟘) ∨ p ⊃ 𝟘) ⊃ 𝟘
  ~~tnd = lam (app hyp (inl (lam (app (wkn hyp) (inr hyp)))))

  -- ~ ~ p ⊃ ~ ~ (p ⊃ q) ⊃ ~ ~ q
  ~~-⊃-mp : ∀ {p q} → [] ⊢
    ((p ⊃ 𝟘) ⊃ 𝟘) ⊃ (((p ⊃ q) ⊃ 𝟘) ⊃ 𝟘) ⊃ (q ⊃ 𝟘) ⊃ 𝟘
  ~~-⊃-mp =
    lam (lam (lam (app (wkn hyp)
                       (lam (app (wkn (wkn (wkn hyp)))
                                 (lam (app (wkn (wkn hyp))
                                      (app (wkn hyp) hyp))))))))

module Semantics1 (Proposition : Set) (kripke : Kripke Proposition) where

  open Logic Proposition
  open Kripke kripke
  open Semantics Proposition kripke

  w⊩a⊃b : ∀ {w a b} → (w ⊩ ⟪ a ⟫ ⊃ ⟪ b ⟫) ≡
    (∀ {w′} → w ≤ w′ → w′ ⊩ᵃ a → w′ ⊩ᵃ b)
  w⊩a⊃b = refl

  w⊩a⊃b⊃a : ∀ {w a b} → (w ⊩ ⟪ a ⟫ ⊃ ⟪ b ⟫ ⊃ ⟪ a ⟫) ≡
    (∀ {w′} → w ≤ w′ → w′ ⊩ᵃ a →
      ∀ {w′′} → w′ ≤ w′′ → w′′ ⊩ᵃ b → w′′ ⊩ᵃ a)
  w⊩a⊃b⊃a = refl

  w⊩a⊃𝟘 : ∀ {w a} → (w ⊩ ⟪ a ⟫ ⊃ 𝟘) ≡
    (∀ {w′} → w ≤ w′ → w′ ⊩ᵃ a → ⊥)
  w⊩a⊃𝟘 = refl

  w⊩𝟘⊃a : ∀ {w a} → (w ⊩ 𝟘 ⊃ ⟪ a ⟫) ≡
    (∀ {w′} → w ≤ w′ → ⊥ → w′ ⊩ᵃ a)
  w⊩𝟘⊃a = refl

module Kripke1 where

  data Prop : Set where
    x : Prop

  data World : Set where
    w0 w1 : World

  data _⊫_ : World → Prop → Set where
    w1x : w1 ⊫ x

  data _≼_ : (w w′ : World) → Set where
    ≼00 : w0 ≼ w0
    ≼11 : w1 ≼ w1
    ≼01 : w0 ≼ w1

  ε : ∀ {w} → w ≼ w
  ε {w0} = ≼00
  ε {w1} = ≼11
 
  _⊙_ : ∀ {w w′ w′′} → w ≼ w′ → w′ ≼ w′′ → w ≼ w′′
  ≼00 ⊙ ≼00 = ≼00
  ≼00 ⊙ ≼01 = ≼01
  ≼01 ⊙ ≼11 = ≼01
  ≼11 ⊙ ≼11 = ≼11

  ⊫-≼ : ∀ {w w′ a} → w ≼ w′ → w ⊫ a → w′ ⊫ a
  ⊫-≼ ≼11 w1x = w1x

  kripke : Kripke Prop
  kripke = record
    { World = World
    ; _≤_ = _≼_
    ; ε = ε
    ; _⊙_ = _⊙_
    ; _⊩ᵃ_ = _⊫_ ;
    ⊩ᵃ-≤ = ⊫-≼ }

  open Soundness Prop kripke

  ~x∨x = ~ ⟪ x ⟫ ∨ ⟪ x ⟫
  ¬w0⊩~x∨x : ¬ (w0 ⊩ ~x∨x)
  ¬w0⊩~x∨x (inj₁ w0⊩⟪x⟫⊃𝟘) = w0⊩⟪x⟫⊃𝟘 ≼01 w1x
  ¬w0⊩~x∨x (inj₂ ())

  ~~x⊃x = ~ ~ ⟪ x ⟫ ⊃ ⟪ x ⟫

  w0⊩~~x : w0 ⊩ ~ ~ ⟪ x ⟫
  w0⊩~~x ≼00 w0⊩~x = w0⊩~x ≼01 w1x
  w0⊩~~x ≼01 w1⊩~x = w1⊩~x ≼11 w1x

  ¬w0⊩~~x⊃x : ¬(w0 ⊩ ~~x⊃x)
  ¬w0⊩~~x⊃x w0⊩~~x⊃x
    with w0⊩~~x⊃x ≼00 w0⊩~~x
  ... | ()

  ¬⊢~~x⊃x : ¬ ([] ⊢ ~~x⊃x)
  ¬⊢~~x⊃x = ¬deducible w0 ~~x⊃x ¬w0⊩~~x⊃x

module Kripke2 where

  data Prop : Set where
    x y : Prop

  data World : Set where
    w0 w1 w2 : World

  data _⊫_ : World → Prop → Set where
    w1x : w1 ⊫ x
    w2y : w2 ⊫ y

  data _≼_ : (w w′ : World) → Set where
    ≼00 : w0 ≼ w0
    ≼11 : w1 ≼ w1
    ≼22 : w2 ≼ w2
    ≼01 : w0 ≼ w1
    ≼02 : w0 ≼ w2

  ε : ∀ {w} → w ≼ w
  ε {w0} = ≼00
  ε {w1} = ≼11
  ε {w2} = ≼22

  _⊙_ : ∀ {w w′ w′′} → w ≼ w′ → w′ ≼ w′′ → w ≼ w′′
  ≼00 ⊙ w′≼w′′ = w′≼w′′
  ≼11 ⊙ w′≼w′′ = w′≼w′′
  ≼22 ⊙ w′≼w′′ = w′≼w′′
  ≼01 ⊙ ≼11 = ≼01
  ≼02 ⊙ ≼22 = ≼02

  ⊫-≼ : ∀ {w w′ a} → w ≼ w′ → w ⊫ a → w′ ⊫ a
  ⊫-≼ ≼11 w1x = w1x
  ⊫-≼ ≼22 w2y = w2y

  kripke : Kripke Prop
  kripke = record
    { World = World
    ; _≤_ = _≼_
    ; ε = ε
    ; _⊙_ = _⊙_
    ; _⊩ᵃ_ = _⊫_ ;
    ⊩ᵃ-≤ = ⊫-≼ }

  open Soundness Prop kripke

  ~[x∧y]⊃~x∨~y = ~ (⟪ x ⟫ ∧ ⟪ y ⟫) ⊃ ~ ⟪ x ⟫ ∨ ~ ⟪ y ⟫

  w0⊩~[x∧y] : w0 ⊩ ~ (⟪ x ⟫ ∧ ⟪ y ⟫)
  w0⊩~[x∧y] ≼00 (() , ())
  w0⊩~[x∧y] ≼01 (w1x , ())
  w0⊩~[x∧y] ≼02 (() , w2y)

  ¬w0⊩~[x∧y]⊃~x∨~y : ¬ (w0 ⊩ ~[x∧y]⊃~x∨~y)
  ¬w0⊩~[x∧y]⊃~x∨~y w0⊩~[x∧y]⊃~x∨~y
    with w0⊩~[x∧y]⊃~x∨~y ≼00 w0⊩~[x∧y]
  ... | inj₁ f = f ≼01 w1x
  ... | inj₂ g = g ≼02 w2y
  
  ¬⊢~[x∧y]⊃~x∨~y : ¬ ([] ⊢ ~[x∧y]⊃~x∨~y)
  ¬⊢~[x∧y]⊃~x∨~y = ¬deducible w0 ~[x∧y]⊃~x∨~y ¬w0⊩~[x∧y]⊃~x∨~y

module Kripke3 where

  data Prop : Set where
    x y : Prop

  data World : Set where
    w0 w1 w2 w3 : World

  data _⊫_ : World → Prop → Set where
    w1y : w1 ⊫ y
    w2x : w2 ⊫ x
    w2y : w2 ⊫ y
    w3x : w3 ⊫ x
    w3y : w3 ⊫ y

  data _≼_ : (w w′ : World) → Set where
    ≼00 : w0 ≼ w0
    ≼11 : w1 ≼ w1
    ≼22 : w2 ≼ w2
    ≼33 : w3 ≼ w3
    ≼01 : w0 ≼ w1
    ≼02 : w0 ≼ w2
    ≼13 : w1 ≼ w3
    ≼23 : w2 ≼ w3
    ≼03 : w0 ≼ w3

  ε : ∀ {w} → w ≼ w
  ε {w0} = ≼00
  ε {w1} = ≼11
  ε {w2} = ≼22
  ε {w3} = ≼33

  _⊙_ : ∀ {w w′ w′′} → w ≼ w′ → w′ ≼ w′′ → w ≼ w′′
  ≼00 ⊙ w′≼w′′ = w′≼w′′
  ≼11 ⊙ w′≼w′′ = w′≼w′′
  ≼22 ⊙ w′≼w′′ = w′≼w′′
  ≼33 ⊙ w′≼w′′ = w′≼w′′
  w≼w′ ⊙ ≼11 = w≼w′
  w≼w′ ⊙ ≼22 = w≼w′
  w≼w′ ⊙ ≼33 = w≼w′
  ≼01 ⊙ ≼13 = ≼03
  ≼02 ⊙ ≼23 = ≼03

  ⊫-≼ : ∀ {w w′ a} → w ≼ w′ → w ⊫ a → w′ ⊫ a
  ⊫-≼ ≼11 w1y = w1y
  ⊫-≼ ≼22 w2x = w2x
  ⊫-≼ ≼22 w2y = w2y
  ⊫-≼ ≼33 w3x = w3x
  ⊫-≼ ≼33 w3y = w3y
  ⊫-≼ ≼13 w1y = w3y
  ⊫-≼ ≼23 w2x = w3x
  ⊫-≼ ≼23 w2y = w3y

  kripke : Kripke Prop
  kripke = record
    { World = World
    ; _≤_ = _≼_
    ; ε = ε
    ; _⊙_ = _⊙_
    ; _⊩ᵃ_ = _⊫_ ;
    ⊩ᵃ-≤ = ⊫-≼ }

  open Soundness Prop kripke

  [x⊃y]⊃~x∨y = (⟪ x ⟫ ⊃ ⟪ y ⟫) ⊃ ~ ⟪ x ⟫ ∨ ⟪ y ⟫

  w0⊩x⊃y : w0 ⊩ ⟪ x ⟫ ⊃ ⟪ y ⟫
  w0⊩x⊃y ≼00 ()
  w0⊩x⊃y ≼01 ()
  w0⊩x⊃y ≼02 w2x = w2y
  w0⊩x⊃y ≼03 w3x = w3y

  ¬w0⊩[x⊃y]⊃~x∨y : ¬ (w0 ⊩ [x⊃y]⊃~x∨y)
  ¬w0⊩[x⊃y]⊃~x∨y w0⊩[x⊃y]⊃~x∨y
    with w0⊩[x⊃y]⊃~x∨y ≼00 w0⊩x⊃y
  ... | inj₁ w0⊩~x = w0⊩~x ≼02 w2x
  ... | inj₂ ()
  
  ¬⊢[x⊃y]⊃~x∨y : ¬ ([] ⊢ [x⊃y]⊃~x∨y)
  ¬⊢[x⊃y]⊃~x∨y = ¬deducible w0 [x⊃y]⊃~x∨y ¬w0⊩[x⊃y]⊃~x∨y
