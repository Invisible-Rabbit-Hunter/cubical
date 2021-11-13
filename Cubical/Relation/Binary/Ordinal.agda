{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Ordinal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Binary.Base

open import Cubical.Induction.WellFounded

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsOrdinal {A : Type ℓ} (_<_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isordinal

  field
    is-set : isSet A
    is-prop-valued : isPropValued _<_

    is-trans : isTrans _<_
    well-founded : WellFounded _<_
    extensional : ∀ a b → (∀ c → (c < a → c < b) × (c < b → c < a)) → a ≡ b

  open WFI well-founded public

unquoteDecl IsOrdinalIsoΣ = declareRecordIsoΣ IsOrdinalIsoΣ (quote IsOrdinal)


record OrdinalStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor ordinalstr

  field
    _<_         : A → A → Type ℓ'
    isOrdinal : IsOrdinal _<_

  infixl 7 _<_

  open IsOrdinal isOrdinal public

Ordinal : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Ordinal ℓ ℓ' = TypeWithStr ℓ (OrdinalStr ℓ')

ordinal : (A : Type ℓ) (_<_ : A → A → Type ℓ') (h : IsOrdinal _<_) → Ordinal ℓ ℓ'
ordinal A _<_ h = A , ordinalstr _<_ h

record IsOrdinalEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : OrdinalStr ℓ₀' A) (e : A ≃ B) (N : OrdinalStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   isposetequiv
  -- Shorter qualified names
  private
    module M = OrdinalStr M
    module N = OrdinalStr N

  field
    pres< : (x y : A) → x M.< y ≃ equivFun e x N.< equivFun e y

  pres⁻¹< : (x y : B) → x N.< y ≃ invEq e x M.< invEq  e y
  pres⁻¹< x y = subst2 (λ x' y' → x' N.< y' ≃ invEq e x M.< invEq e y)
                       (secEq e x) (secEq e y)
                       (invEquiv (pres< (invEq e x) (invEq e y)))

OrdinalEquiv : (M : Ordinal ℓ₀ ℓ₀') (M : Ordinal ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
OrdinalEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsOrdinalEquiv (M .snd) e (N .snd)

isPropIsOrdinal : {A : Type ℓ} (_<_ : A → A → Type ℓ') → isProp (IsOrdinal _<_)
isPropIsOrdinal _<_ = isOfHLevelRetractFromIso 1 IsOrdinalIsoΣ
  (isPropΣ isPropIsSet λ isSetA →
    isPropΣ (isPropΠ2 λ _ _ → isPropIsProp) λ isPropValued< →
    isProp×2 (isPropΠ5 λ _ _ _ _ _ → isPropValued< _ _)
             (isPropΠ isPropAcc)
             (isPropΠ3 λ _ _ _ → isSetA _ _))

𝒮ᴰ-Ordinal : DUARel (𝒮-Univ ℓ) (OrdinalStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Ordinal =
  𝒮ᴰ-Record (𝒮-Univ _) IsOrdinalEquiv
    (fields:
      data[ _<_ ∣ autoDUARel _ _ ∣ pres< ]
      prop[ isOrdinal ∣ (λ _ _ → isPropIsOrdinal _) ])
    where
    open OrdinalStr
    open IsOrdinal
    open IsOrdinalEquiv

PosetPath : (M N : Ordinal ℓ ℓ') → OrdinalEquiv M N ≃ (M ≡ N)
PosetPath = ∫ 𝒮ᴰ-Ordinal .UARel.ua

-- an easier way of establishing an equivalence of posets
module _ {P : Ordinal ℓ₀ ℓ₀'} {S : Ordinal ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = OrdinalStr (P .snd)
    module S = OrdinalStr (S .snd)

  module _ (isMon : ∀ x y → x P.< y → equivFun e x S.< equivFun e y)
           (isMonInv : ∀ x y → x S.< y → invEq e x P.< invEq e y) where
    open IsOrdinalEquiv
    open IsOrdinal

    makeIsOrdinalEquiv : IsOrdinalEquiv (P .snd) e (S .snd)
    pres< makeIsOrdinalEquiv x y = propBiimpl→Equiv (P.isOrdinal .is-prop-valued _ _)
                                                    (S.isOrdinal .is-prop-valued _ _)
                                                    (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.< equivFun e y → x P.< y
      isMonInv' x y ex≤ey = transport (λ i → retEq e x i P.< retEq e y i) (isMonInv _ _ ex≤ey)

module _ {M : Ordinal ℓ₀ ℓ₀'} {N : Ordinal ℓ₁ ℓ₁'} (f g : OrdinalEquiv M N) where
  private
    module M = OrdinalStr (snd M)
    module N = OrdinalStr (snd N)
    module f = IsOrdinalEquiv (snd f)
    module g = IsOrdinalEquiv (snd g)

  OrdinalEquiv-unique-value : ∀ (x : ⟨ M ⟩) → equivFun (fst f) x ≡ equivFun (fst g) x
  OrdinalEquiv-unique-value =
    M.induction λ x rec →
    N.extensional _ _ λ c →
      (λ c<fx → let ff⁻¹c≡c = secEq (fst f) c
                    ff⁻¹c<fx = subst⁻ (λ a → a N.< equivFun (fst f) x) ff⁻¹c≡c c<fx
                    f⁻¹c<x = invEq (f.pres< (invEq (fst f) c) x) ff⁻¹c<fx
                    c≡gf⁻¹c = sym ff⁻¹c≡c ∙ rec (invEq (fst f) c) f⁻¹c<x
                    g⁻¹c≡f⁻¹c = {!   !}
                in {! equivFun (g.pres< ? ?) ?  !}) ,
      {!   !}


-- module PosetReasoning (P' : Ordinal ℓ ℓ') where
--  private P = fst P'
--  open OrdinalStr (snd P')
--  open IsOrdinal

--  _≤⟨_⟩_ : (x : P) {y z : P} → x < y → y < z → x < z
--  x ≤⟨ p ⟩ q = isOrdinal .is-trans x _ _ p q

--  _◾ : (x : P) → x < x
--  x ◾ = isOrdinal .is-refl x

--  infixr 0 _≤⟨_⟩_
--  infix  1 _◾
