{-# OPTIONS --cubical --guardedness #-}

module WLPO where 

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order 
open <-Reasoning

_↔_ : Type → Type → Type 
A ↔ B = (A → B) × (B → A)

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base as TV

binarySequence : Type 
binarySequence = ℕ → Bool

zeroSequence : binarySequence 
zeroSequence _ = false

evaluate : {A : Type} → (A → Bool) → BoolHom ( freeBA A ) BoolBR
evaluate {A} α = inducedBAHom A BoolBR α 

_$freeℕ_ : binarySequence → freeBATerms ℕ → Bool
_$freeℕ_ α a = evaluate α $cr fst includeBATermsSurj a 

>maxUsedIndex : (a : freeBATerms ℕ) → ℕ 
>maxUsedIndex (Tvar n)   = suc n
>maxUsedIndex (Tconst x) = 0
>maxUsedIndex (a +T b)   = max (>maxUsedIndex a) (>maxUsedIndex b)
>maxUsedIndex (-T a)     = >maxUsedIndex a
>maxUsedIndex (a ·T b)   = max (>maxUsedIndex a) (>maxUsedIndex b) 

δ : ℕ → binarySequence 
δ zero zero       = true
δ (suc n) zero    = false
δ zero (suc m)    = false
δ (suc n) (suc m) = δ n m 

δSnn=false : (n : ℕ ) → δ (suc n ) n ≡ false
δSnn=false zero    = refl
δSnn=false (suc n) = δSnn=false n 

δnn=true : (n : ℕ) → δ n n ≡ true
δnn=true zero    = refl
δnn=true (suc n) = δnn=true n 

miss : (a : freeBATerms ℕ) → binarySequence
miss = δ ∘ >maxUsedIndex 

_ignores_ : binarySequence → freeBATerms ℕ → Type _
α ignores a = α $freeℕ a ≡ zeroSequence $freeℕ a

opaque
  unfolding TV.var
  unfolding equalityFromEqualityOnGenerators 
  unfolding inducedBAHom
  ignoreAtoms : (n m : ℕ) → (suc m ≤ n) → δ n ignores (Tvar m)
  ignoreAtoms zero _          x = ex-falso (¬-<-zero x)
  ignoreAtoms (suc n) zero    _ = refl 
  ignoreAtoms (suc n) (suc m) x = ignoreAtoms n m (predℕ-≤-predℕ x) 

  ignoreSmallTerms : (n : ℕ) → (a : freeBATerms ℕ) → (>maxUsedIndex a ≤ n) → δ n $freeℕ a ≡ zeroSequence $freeℕ a
  ignoreSmallTerms n (Tvar m)   p = ignoreAtoms n m p
  ignoreSmallTerms _ (Tconst x) _ = refl
  ignoreSmallTerms n (a +T b)   p = cong₂ _⊕_
      (ignoreSmallTerms n a (>maxUsedIndex a ≤⟨ left-≤-max {>maxUsedIndex a} {>maxUsedIndex b} ⟩ max (>maxUsedIndex a) (>maxUsedIndex b) ≤≡⟨ p ⟩ n ∎))
      (ignoreSmallTerms n b (>maxUsedIndex b ≤⟨ right-≤-max {>maxUsedIndex b} {>maxUsedIndex a} ⟩ max (>maxUsedIndex a) (>maxUsedIndex b) ≤≡⟨ p ⟩ n ∎))
  ignoreSmallTerms n (-T a)     p = ignoreSmallTerms n a p
  ignoreSmallTerms n (a ·T b)   p = cong₂ _and_
      (ignoreSmallTerms n a (>maxUsedIndex a ≤⟨ left-≤-max {>maxUsedIndex a} {>maxUsedIndex b} ⟩ max (>maxUsedIndex a) (>maxUsedIndex b) ≤≡⟨ p ⟩ n ∎))
      (ignoreSmallTerms n b (>maxUsedIndex b ≤⟨ right-≤-max {>maxUsedIndex b} {>maxUsedIndex a} ⟩ max (>maxUsedIndex a) (>maxUsedIndex b) ≤≡⟨ p ⟩ n ∎))
  
  missMisses : (a : freeBATerms ℕ) → (miss a) ignores a
  missMisses a = ignoreSmallTerms (>maxUsedIndex a) a (0 , refl) 

module PlayingWithWLPO  
 (f     : binarySequence → Bool) 
 (WLPOf : (α : binarySequence) → ((f α ≡ false) ↔ (∀ (n : ℕ ) → α n ≡ false) ))
 (d     : freeBATerms ℕ) 
 (SD    : (α : binarySequence) → ( f α ≡ (α $freeℕ d) ))
 where
  fmiss=1 : f (miss d) ≡ true
  fmiss=1 = ¬false→true (f (miss d)) λ x → true≢false 
    (true                      ≡⟨ sym $ δnn=true         (>maxUsedIndex d) ⟩ 
     miss d (>maxUsedIndex d)  ≡⟨ fst (WLPOf (miss d)) x (>maxUsedIndex d) ⟩ 
     false ∎ )

  fzeroseq=0 : f zeroSequence ≡ false
  fzeroseq=0 = (snd $ WLPOf zeroSequence) λ n → refl 

  fmiss=fZeroSeq : f (miss d ) ≡ f zeroSequence
  fmiss=fZeroSeq = f (miss d)  
              ≡⟨ SD (miss d) ⟩ 
            (miss d) $freeℕ d 
              ≡⟨ missMisses d ⟩ 
            (zeroSequence $freeℕ d) 
              ≡⟨ (sym $ SD zeroSequence) ⟩ 
            f zeroSequence ∎

  contradiction : ⊥
  contradiction = true≢false $ true ≡⟨ sym fmiss=1 ⟩ f (miss d) ≡⟨ fmiss=fZeroSeq ⟩ f zeroSequence ≡⟨ fzeroseq=0 ⟩ false ∎ 
  
module PlayingWithWLPO'
 (f : binarySequence → Bool) 
 (WLPOf : ((α : binarySequence) → ((f α ≡ false) ↔ (∀ (n : ℕ ) → α n ≡ false))))
 (c : ⟨ freeBA ℕ ⟩) 
 (SD :    (α : binarySequence) → ( f α ≡ evaluate α $cr c ))
 where
 contradiction' : ⊥ 
 contradiction' = PT.rec isProp⊥ (λ { (t , πt≡c) → PlayingWithWLPO.contradiction f WLPOf t 
   λ { α →  f α ≡⟨ SD α ⟩ 
            evaluate α $cr c ≡⟨ cong (λ e → evaluate α $cr e) (sym πt≡c)  ⟩ 
            (α $freeℕ t) ∎  } }) 
            (snd includeBATermsSurj c) 
