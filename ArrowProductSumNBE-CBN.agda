module ArrowProductSumNBE-CBN where

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

module Logic (Atomic : Set) where

  infix 3 _⊢_ _⊢ʳ_ _⊢ᵉ_
  infixr 4 _⊃_
  infixr 6 _∧_
  infixr 5 _∨_

  -- Syntax

  data Formula : Set where
    ⟪_⟫  : (a : Atomic) → Formula
    _⊃_ : (p q : Formula) → Formula
    _∧_ : (p q : Formula) → Formula
    _∨_ : (p q : Formula) → Formula

  Ctx = List Formula

  data _⊢_ : Ctx → Formula → Set where
    hyp : ∀ {Γ p} → p ∷ Γ ⊢ p
    wkn : ∀ {Γ p q} → Γ ⊢ p → q ∷ Γ ⊢ p
    lam  : ∀ {Γ p q} → p ∷ Γ ⊢ q → Γ ⊢ p ⊃ q
    app  : ∀ {Γ p q} → Γ ⊢ p ⊃ q → Γ ⊢ p → Γ ⊢ q
    pair : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ q → Γ ⊢ p ∧ q
    fst : ∀ {Γ p q} → Γ ⊢ p ∧ q → Γ ⊢ p
    snd : ∀ {Γ p q} → Γ ⊢ p ∧ q → Γ ⊢ q
    inl : ∀ {Γ p q} → Γ ⊢ p → Γ ⊢ (p ∨ q)
    inr : ∀ {Γ p q} → Γ ⊢ q → Γ ⊢ (p ∨ q)
    case : ∀ {Γ p q r} → Γ ⊢ p ∨ q → p ∷ Γ ⊢ r → q ∷ Γ ⊢ r → Γ ⊢ r

  -- Target language: natural deduction allowing only beta-normal forms

  mutual

    data _⊢ʳ_ : Ctx → Formula → Set where
      ne : ∀ {Γ p} → Γ ⊢ᵉ p → Γ ⊢ʳ p
      lam : ∀ {Γ p q} → p ∷ Γ ⊢ʳ q → Γ ⊢ʳ p ⊃ q
      pair : ∀ {Γ p q} → Γ ⊢ʳ p → Γ ⊢ʳ q → Γ ⊢ʳ p ∧ q
      inl : ∀ {Γ p q} → Γ ⊢ʳ p → Γ ⊢ʳ p ∨ q
      inr : ∀ {Γ p q} → Γ ⊢ʳ q → Γ ⊢ʳ p ∨ q

    data _⊢ᵉ_ : Ctx → Formula → Set where
      hyp : ∀ {Γ p} → p ∷ Γ ⊢ᵉ p
      wkn : ∀ {Γ p q} → Γ ⊢ʳ p → q ∷ Γ ⊢ᵉ p
      app : ∀ {Γ p q} → Γ ⊢ᵉ p ⊃ q → Γ ⊢ʳ p → Γ ⊢ᵉ q
      fst : ∀ {Γ p q} → Γ ⊢ᵉ p ∧ q → Γ ⊢ᵉ p
      snd : ∀ {Γ p q} → Γ ⊢ᵉ p ∧ q → Γ ⊢ᵉ q
      case : ∀ {Γ p q r} →
               Γ ⊢ᵉ p ∨ q → p ∷ Γ ⊢ʳ r → q ∷ Γ ⊢ʳ r → Γ ⊢ᵉ r

-- Worlds (Kripke structures)

record Kripke (Proposition : Set) : Set₁ where
  field
    World : Set
    _≤_ : World → World → Set
    ε : ∀ {w} → w ≤ w
    _⊙_ : ∀ {w w′ w′′} → w ≤ w′ → w′ ≤ w′′ → w ≤ w′′
    _⊩ᵃ_ : World → Proposition → Set
    ⊩ᵃ≤ : ∀ {a w w′} → w ≤ w′ → w ⊩ᵃ a → w′ ⊩ᵃ a

module Semantics
  (Atomic : Set)
  (kripke : Kripke (Logic.Formula Atomic)) where

  open Logic Atomic
  open Kripke kripke

  infix 3 _⊩ˢ_ _⊩_ _⊪_

  mutual

    _⊩ˢ_ : World → Formula → Set
    w ⊩ˢ ⟪ a ⟫ = w ⊩ᵃ ⟪ a ⟫
    w ⊩ˢ p ⊃ q = ∀ {w′} → w ≤ w′ → w′ ⊩ p → w′ ⊩ q
    w ⊩ˢ p ∧ q = w ⊩ p × w ⊩ q
    w ⊩ˢ p ∨ q = w ⊩ p ⊎ w ⊩ q

    _⊩_ : World → Formula → Set
    w ⊩ p = (r : Formula) →
      ∀ {w′} → w ≤ w′ →
      (∀ {w′′} → w′ ≤ w′′ → w′′ ⊩ˢ p → w′′ ⊩ᵃ r) →
      w′ ⊩ᵃ r

  _⊪_ : World → Ctx → Set
  w ⊪ [] = ⊤
  w ⊪ (p ∷ Γ) = w ⊩ p × w ⊪ Γ

  ⊩≤ : ∀ p {w w′} → w ≤ w′ → w ⊩ p → w′ ⊩ p
  ⊩≤ p ≤′ w⊩p r ≤′′ k = w⊩p r (≤′ ⊙ ≤′′) k

  ⊩ˢ≤ : ∀ p {w w′} → w ≤ w′ → w ⊩ˢ p → w′ ⊩ˢ p
  ⊩ˢ≤ ⟪ a ⟫ = ⊩ᵃ≤
  ⊩ˢ≤ (p ⊃ q) ≤′ w⊩ˢp⊃q ≤′′ =
    w⊩ˢp⊃q (≤′ ⊙ ≤′′)
  ⊩ˢ≤ (p ∧ q) ≤′ =
    Prod.map (⊩≤ p ≤′) (⊩≤ q ≤′)
  ⊩ˢ≤ (p ∨ q) ≤′ =
    Sum.map (⊩≤ p ≤′) (⊩≤ q ≤′)

  ⊪≤ : ∀ Γ {w w′} → w ≤ w′ → w ⊪ Γ → w′ ⊪ Γ
  ⊪≤ [] ≤′ tt = tt
  ⊪≤ (p ∷ Γ) ≤′ =
    Prod.map (⊩≤ p ≤′) (⊪≤ Γ ≤′)

module Soundness
  (Atomic : Set)
  (kripke : Kripke (Logic.Formula Atomic)) where

  open Logic Atomic
  open Kripke kripke
  open Semantics Atomic kripke

  return : ∀ p {w} → w ⊩ˢ p → w ⊩ p
  return p w⊩ˢp r ≤′ k =
    k ε (⊩ˢ≤ p ≤′ w⊩ˢp)

  bind : ∀ p r {w} → w ⊩ p → (∀ {w′} → w ≤ w′ → w′ ⊩ˢ p → w′ ⊩ r) → w ⊩ r
  bind p r w⊩p k r′ ≤′ k′ =
    w⊩p r′ ≤′
      (λ ≤′′ w′′⊩ˢp → k (≤′ ⊙ ≤′′) w′′⊩ˢp r′ ε
        (λ ≤′′′ → k′ (≤′′ ⊙ ≤′′′)))


  soundness : ∀ {Γ p} → Γ ⊢ p → ∀ {w} → w ⊪ Γ → w ⊩ p
  soundness hyp (w⊩p , w⊪Γ) =
    w⊩p
  soundness (wkn Γ⊢p) (w⊩q , w⊪Γ) =
    soundness Γ⊢p w⊪Γ
  soundness (lam {Γ} {p} {q} p∷Γ⊢q) w⊪Γ =
    return (p ⊃ q) (λ ≤′ w′⊩p → soundness p∷Γ⊢q (w′⊩p , ⊪≤ Γ ≤′ w⊪Γ))
  soundness (app {Γ} {p} {q} Γ⊢p⊃q Γ⊢p) w⊪Γ =
    bind (p ⊃ q) q (soundness Γ⊢p⊃q w⊪Γ)
      (λ ≤′ kpq → kpq ε (soundness Γ⊢p (⊪≤ Γ ≤′ w⊪Γ)))
  soundness (pair {Γ} {p} {q} Γ⊢p Γ⊢q) {w} w⊪Γ =
    return (p ∧ q) (soundness Γ⊢p w⊪Γ , soundness Γ⊢q w⊪Γ)
  soundness (fst {Γ} {p} {q} Γ⊢p∧q) w⊪Γ =
    bind (p ∧ q) p (soundness Γ⊢p∧q w⊪Γ) (λ ≤′ w′⊩p∧q → proj₁ w′⊩p∧q)
  soundness (snd {Γ} {p} {q} Γ⊢p∧q) {w} w⊪Γ =
    bind (p ∧ q) q (soundness Γ⊢p∧q w⊪Γ) (λ ≤′ w′⊩p∧q → proj₂ w′⊩p∧q)
  soundness (inl {Γ} {p} {q} Γ⊢p) {w} w⊪Γ =
    return (p ∨ q) (inj₁ (soundness Γ⊢p w⊪Γ))
  soundness (inr {Γ} {p} {q} Γ⊢q) {w} w⊪Γ =
    return (p ∨ q) (inj₂ (soundness Γ⊢q w⊪Γ))
  soundness (case {Γ} {p} {q} {r} Γ⊢p∨q p∷Γ⊢r q∷Γ⊢r) {w} w⊪Γ =
    bind (p ∨ q) r (soundness Γ⊢p∨q w⊪Γ)
      (λ ≤′ → [ (λ w′⊩p → soundness p∷Γ⊢r (w′⊩p , ⊪≤ Γ ≤′ w⊪Γ)) ,
                 (λ w′⊩q → soundness q∷Γ⊢r (w′⊩q , ⊪≤ Γ ≤′ w⊪Γ)) ]′)

module Completeness (Atomic : Set) where

  open Logic Atomic

  data _≼_ : (Γ Γ′ : Ctx) → Set where 
    ≼-refl : ∀ {Γ} → Γ ≼ Γ
    ≼-cons : ∀ {Γ Γ′ p} → Γ ≼ Γ′ → Γ ≼ (p ∷ Γ′)

  δ : ∀ {Γ p} → Γ ≼ (p ∷ Γ)
  δ = ≼-cons ≼-refl

  ≼-trans : ∀ {Γ Γ′ Γ′′} → Γ ≼ Γ′ → Γ′ ≼ Γ′′ → Γ ≼ Γ′′
  ≼-trans ≼′ ≼-refl = ≼′
  ≼-trans ≼′ (≼-cons ≼′′) = ≼-cons (≼-trans ≼′ ≼′′)

  ⊢ᵉ≼ : ∀ {p Γ Γ′} → Γ ≼ Γ′ → Γ ⊢ᵉ p → Γ′ ⊢ᵉ p
  ⊢ᵉ≼ ≼-refl Γ′⊢ᵉp = Γ′⊢ᵉp
  ⊢ᵉ≼ (≼-cons ≼′) Γ⊢ᵉp = wkn (ne (⊢ᵉ≼ ≼′ Γ⊢ᵉp))

  ⊢ʳ≼ : ∀ {p Γ Γ′} → Γ ≼ Γ′ → Γ ⊢ʳ p → Γ′ ⊢ʳ p
  ⊢ʳ≼ ≼-refl Γ⊢ʳp = Γ⊢ʳp
  ⊢ʳ≼ (≼-cons ≼′) Γ⊢ʳp = ne (wkn (⊢ʳ≼ ≼′ Γ⊢ʳp))

  uks : Kripke Formula
  uks = record
    { World = Ctx
    ; _≤_ = _≼_
    ; ε = ≼-refl
    ; _⊙_ = ≼-trans
    ; _⊩ᵃ_ = _⊢ʳ_
    ; ⊩ᵃ≤ = ⊢ʳ≼
    }

  open Kripke uks
  open Semantics Atomic uks
  open Soundness Atomic uks

  mutual

    reify : ∀ {Γ} p → Γ ⊩ p → Γ ⊢ʳ p
    reify ⟪ a ⟫ Γ⊩⟪a⟫ =
      Γ⊩⟪a⟫ ⟪ a ⟫ ≼-refl (λ ≼′ Γ′⊩ᵃ⟪a⟫ → Γ′⊩ᵃ⟪a⟫)
    reify (p ⊃ q) Γ⊩p⊃q =
      Γ⊩p⊃q (p ⊃ q) ≼-refl (λ ≼′ kpq →
        lam (reify q (kpq (≼-cons ≼-refl) (reflect p hyp))) )
    reify (p ∧ q) Γ⊩p∧q =
      Γ⊩p∧q (p ∧ q) ε
        (λ ≼′ Γ′⊩p∧q →
          pair (reify p (proj₁ Γ′⊩p∧q)) (reify q (proj₂ Γ′⊩p∧q)))
    reify (p ∨ q) Γ⊩p∨q =
      Γ⊩p∨q (p ∨ q) ≼-refl (λ ≼′ →
        [ (λ Γ′⊩p → inl (reify p Γ′⊩p)) , (λ Γ′⊩q → inr (reify q Γ′⊩q)) ]′)

    reflect : ∀ {Γ} p → Γ ⊢ᵉ p → Γ ⊩ p
    reflect ⟪ a ⟫ Γ⊢ᵉ⟪a⟫ r ≼′ k =
      k ≼-refl (ne Γ′⊢ᵉ⟪a⟫)
      where Γ′⊢ᵉ⟪a⟫ = ⊢ᵉ≼ ≼′ Γ⊢ᵉ⟪a⟫
    reflect (p ⊃ q) Γ⊢ᵉp⊃q r ≼′ k =
      k ≼-refl (λ ≼′′ Γ′′⊩p →
        reflect q (app (⊢ᵉ≼ (≼′ ⊙ ≼′′) Γ⊢ᵉp⊃q) (reify p Γ′′⊩p)))
    reflect (p ∧ q) Γ⊢ᵉp∧q r ≼′ k =
      k ≼-refl (reflect p (fst Γ′⊢ᵉp∧q) , reflect q (snd Γ′⊢ᵉp∧q))
      where Γ′⊢ᵉp∧q = ⊢ᵉ≼ ≼′ Γ⊢ᵉp∧q
    reflect (p ∨ q) Γ⊢ᵉp∨q r {Γ′} ≼′ k =
      ne (case Γ′⊢ᵉp∨q
               (k (≼-cons ≼-refl) (inj₁ (reflect p hyp)))
               (k (≼-cons ≼-refl) (inj₂ (reflect q hyp))))
      where Γ′⊢ᵉp∨q = ⊢ᵉ≼ ≼′ Γ⊢ᵉp∨q

  reflect-context : (Γ : Ctx) → Γ ⊪ Γ
  reflect-context [] = tt
  reflect-context (p ∷ Γ) =
    reflect p hyp , ⊪≤ Γ (≼-cons ≼-refl) (reflect-context Γ)

  nbe : ∀ {Γ p} → Γ ⊢ p → Γ ⊢ʳ p
  nbe {Γ} {p} Γ⊢p = reify p (soundness Γ⊢p (reflect-context Γ))
