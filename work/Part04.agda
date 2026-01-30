{-# OPTIONS --cubical --guardedness #-}

module work.Part04 where

-- =============================================================================
-- Part 04: Cantor Pairing, openAnd, closedDeMorgan, closedOr
-- =============================================================================

-- Import Part03 for base definitions (includes Part01 and Part02)
open import work.Part03 public

-- Additional imports needed for this part
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun; _∘_; uncurry)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isProp×; isSetΣSndProp; isSetΠ)
open import Cubical.Data.Sigma using (Σ≡Prop; _×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ; +-suc; +-zero; +-comm)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary
import Cubical.Induction.WellFounded as WF

-- =============================================================================
-- Section 17: Countable closure properties (lines 1867-2390)
-- =============================================================================

-- The inspect idiom for capturing equalities from with-abstractions
data Reveal_·_is_ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) (y : B x) : Type₀ where
  [_] : f x ≡ y → Reveal f · x is y

inspect : ∀ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) → Reveal f · x is (f x)
inspect f x = [ refl ]

-- Cantor pairing function: ⟨m, n⟩ = (m + n)(m + n + 1)/2 + n
-- The bijectivity is fully proved below using findDiagonal helper

-- Triangular number: T(n) = 0 + 1 + ... + n = n(n+1)/2
-- This is the number of elements before diagonal n
triangular : ℕ → ℕ
triangular zero = zero
triangular (suc n) = suc n +ℕ triangular n

-- Cantor pairing: ⟨m, n⟩ = triangular(m + n) + n
cantorPair : ℕ → ℕ → ℕ
cantorPair m n = triangular (m +ℕ n) +ℕ n

-- Boolean less-than for natural numbers (local version)
_<ᵇ'_ : ℕ → ℕ → Bool
zero <ᵇ' zero = false
zero <ᵇ' suc n = true
suc m <ᵇ' zero = false
suc m <ᵇ' suc n = m <ᵇ' n

-- Helper: find diagonal w given k, using fuel
findDiagonal : ℕ → ℕ → ℕ → ℕ
findDiagonal zero k diag = diag
findDiagonal (suc fuel) k diag =
  if k <ᵇ' triangular (suc diag)
  then diag
  else findDiagonal fuel k (suc diag)

-- Cantor unpairing
cantorUnpair : ℕ → ℕ × ℕ
cantorUnpair k =
  let w = findDiagonal (suc k) k 0
      n = k ∸ triangular w
      m = w ∸ n
  in (m , n)

-- Lemmas about boolean comparison
<ᵇ'-reflects : (m n : ℕ) → m <ᵇ' n ≡ true → m < n
<ᵇ'-reflects zero zero p = ex-falso (false≢true p)
<ᵇ'-reflects zero (suc n) _ = suc-≤-suc zero-≤
<ᵇ'-reflects (suc m) zero p = ex-falso (false≢true p)
<ᵇ'-reflects (suc m) (suc n) p = suc-≤-suc (<ᵇ'-reflects m n p)

¬<ᵇ'-reflects : (m n : ℕ) → m <ᵇ' n ≡ false → n ≤ m
¬<ᵇ'-reflects zero zero _ = ≤-refl
¬<ᵇ'-reflects zero (suc n) p = ex-falso (true≢false p)
¬<ᵇ'-reflects (suc m) zero _ = zero-≤
¬<ᵇ'-reflects (suc m) (suc n) p = suc-≤-suc (¬<ᵇ'-reflects m n p)

-- Arithmetic lemmas
+∸-cancel : (a b : ℕ) → (a +ℕ b) ∸ b ≡ a
+∸-cancel a zero = +-zero a
+∸-cancel a (suc b) =
  (a +ℕ suc b) ∸ suc b   ≡⟨ cong (_∸ suc b) (+-suc a b) ⟩
  suc (a +ℕ b) ∸ suc b   ≡⟨ refl ⟩
  (a +ℕ b) ∸ b           ≡⟨ +∸-cancel a b ⟩
  a                      ∎

∸+-cancel : (a b : ℕ) → b ≤ a → (a ∸ b) +ℕ b ≡ a
∸+-cancel a zero _ = +-zero a
∸+-cancel zero (suc b) sb≤0 = ex-falso (¬-<-zero sb≤0)
∸+-cancel (suc a) (suc b) sb≤sa =
  (suc a ∸ suc b) +ℕ suc b   ≡⟨ refl ⟩
  (a ∸ b) +ℕ suc b           ≡⟨ +-suc (a ∸ b) b ⟩
  suc ((a ∸ b) +ℕ b)         ≡⟨ cong suc (∸+-cancel a b (pred-≤-pred sb≤sa)) ⟩
  suc a ∎

triangular≤cantorPair : (m n : ℕ) → triangular (m +ℕ n) ≤ cantorPair m n
triangular≤cantorPair m n = ≤-+k-local (triangular (m +ℕ n)) n
  where
  ≤-+k-local : (a b : ℕ) → a ≤ a +ℕ b
  ≤-+k-local a zero = subst (a ≤_) (sym (+-zero a)) ≤-refl
  ≤-+k-local a (suc b) =
    let step1 : a ≤ a +ℕ b
        step1 = ≤-+k-local a b
        step2 : a ≤ suc (a +ℕ b)
        step2 = ≤-suc step1
    in subst (a ≤_) (sym (+-suc a b)) step2

cantorPair<triangular-suc : (m n : ℕ) → cantorPair m n < triangular (suc (m +ℕ n))
cantorPair<triangular-suc m n = goal
  where
  w = m +ℕ n

  n≤w : n ≤ w
  n≤w = n≤m+n-local m n
    where
    n≤m+n-local : (a b : ℕ) → b ≤ a +ℕ b
    n≤m+n-local zero b = ≤-refl
    n≤m+n-local (suc a) b = ≤-trans (n≤m+n-local a b) ≤-sucℕ

  sucn≤sucw : suc n ≤ suc w
  sucn≤sucw = suc-≤-suc n≤w

  step1 : triangular w +ℕ suc n ≤ triangular w +ℕ suc w
  step1 = ≤-+k-mono (triangular w) (suc n) (suc w) sucn≤sucw
    where
    ≤-+k-mono : (a b c : ℕ) → b ≤ c → a +ℕ b ≤ a +ℕ c
    ≤-+k-mono zero b c b≤c = b≤c
    ≤-+k-mono (suc a) b c b≤c = suc-≤-suc (≤-+k-mono a b c b≤c)

  eq1 : suc (triangular w +ℕ n) ≡ triangular w +ℕ suc n
  eq1 = sym (+-suc (triangular w) n)

  eq2 : triangular w +ℕ suc w ≡ suc w +ℕ triangular w
  eq2 = +-comm (triangular w) (suc w)

  eq3 : suc w +ℕ triangular w ≡ triangular (suc w)
  eq3 = refl

  goal : suc (triangular w +ℕ n) ≤ triangular (suc w)
  goal = subst (_≤ triangular (suc w)) (sym eq1)
           (subst (triangular w +ℕ suc n ≤_) (eq2 ∙ eq3) step1)

<-reflects-<ᵇ' : (a b : ℕ) → a < b → a <ᵇ' b ≡ true
<-reflects-<ᵇ' zero zero 1≤0 = ex-falso (¬-<-zero 1≤0)
<-reflects-<ᵇ' zero (suc b) _ = refl
<-reflects-<ᵇ' (suc a) zero sa<0 = ex-falso (¬-<-zero sa<0)
<-reflects-<ᵇ' (suc a) (suc b) sa<sb = <-reflects-<ᵇ' a b (pred-≤-pred sa<sb)

cantorPair<ᵇ'-triangular-suc : (m n : ℕ) → cantorPair m n <ᵇ' triangular (suc (m +ℕ n)) ≡ true
cantorPair<ᵇ'-triangular-suc m n = <-reflects-<ᵇ' _ _ (cantorPair<triangular-suc m n)

cantorPair-triangular-diff : (m n : ℕ) → cantorPair m n ∸ triangular (m +ℕ n) ≡ n
cantorPair-triangular-diff m n = +∸-cancel' n (triangular (m +ℕ n))
  where
  +∸-cancel' : (a b : ℕ) → (b +ℕ a) ∸ b ≡ a
  +∸-cancel' a zero = refl
  +∸-cancel' a (suc b) = +∸-cancel' a b

m+n∸n≡m : (m n : ℕ) → (m +ℕ n) ∸ n ≡ m
m+n∸n≡m m zero = +-zero m
m+n∸n≡m m (suc n) =
  (m +ℕ suc n) ∸ suc n   ≡⟨ cong (_∸ suc n) (+-suc m n) ⟩
  suc (m +ℕ n) ∸ suc n   ≡⟨ refl ⟩
  (m +ℕ n) ∸ n           ≡⟨ m+n∸n≡m m n ⟩
  m ∎

triangular-suc : (n : ℕ) → triangular n < triangular (suc n)
triangular-suc n = ≤-+k-mono-l 1 (suc n) (triangular n) (suc-≤-suc zero-≤)
  where
  ≤-+k-mono-l : (a b c : ℕ) → a ≤ b → a +ℕ c ≤ b +ℕ c
  ≤-+k-mono-l zero b c _ = ≤-+k-r b c
    where
    ≤-+k-r : (x y : ℕ) → y ≤ x +ℕ y
    ≤-+k-r zero y = ≤-refl
    ≤-+k-r (suc x) y = ≤-trans (≤-+k-r x y) ≤-sucℕ
  ≤-+k-mono-l (suc a) zero c sa≤0 = ex-falso (¬-<-zero sa≤0)
  ≤-+k-mono-l (suc a) (suc b) c sa≤sb = suc-≤-suc (≤-+k-mono-l a b c (pred-≤-pred sa≤sb))

triangular-mono-< : (n m : ℕ) → n < m → triangular n < triangular m
triangular-mono-< n zero n<0 = ex-falso (¬-<-zero n<0)
triangular-mono-< n (suc m) sn≤sm with n ≟ m
... | lt n<m = <-trans (triangular-mono-< n m n<m) (triangular-suc m)
... | eq n≡m = subst (λ x → triangular x < triangular (suc m)) (sym n≡m) (triangular-suc m)
... | gt m<n = ex-falso (¬m<m (≤-trans m<n (pred-≤-pred sn≤sm)))

triangular-mono-≤ : (n m : ℕ) → n ≤ m → triangular n ≤ triangular m
triangular-mono-≤ n m n≤m with n ≟ m
... | lt n<m = <-weaken (triangular-mono-< n m n<m)
... | eq n≡m = subst (λ x → triangular n ≤ triangular x) n≡m ≤-refl
... | gt m<n = ex-falso (¬m<m (≤-trans m<n n≤m))

k≥triangular-suc-acc : (k w acc : ℕ) → acc < w → triangular w ≤ k
                     → triangular (suc acc) ≤ k
k≥triangular-suc-acc k w acc acc<w Tw≤k =
  ≤-trans (triangular-mono-≤ (suc acc) w acc<w) Tw≤k

k≮ᵇ'triangular-suc-acc : (k w acc : ℕ) → acc < w → triangular w ≤ k
                      → k <ᵇ' triangular (suc acc) ≡ false
k≮ᵇ'triangular-suc-acc k w acc acc<w Tw≤k = ≤-reflects-¬<ᵇ' _ _ (k≥triangular-suc-acc k w acc acc<w Tw≤k)
  where
  ≤-reflects-¬<ᵇ' : (a b : ℕ) → b ≤ a → a <ᵇ' b ≡ false
  ≤-reflects-¬<ᵇ' zero zero _ = refl
  ≤-reflects-¬<ᵇ' (suc a) zero _ = refl
  ≤-reflects-¬<ᵇ' zero (suc b) sb≤0 = ex-falso (¬-<-zero sb≤0)
  ≤-reflects-¬<ᵇ' (suc a) (suc b) sb≤sa = ≤-reflects-¬<ᵇ' a b (pred-≤-pred sb≤sa)

findDiagonal-found : (fuel k diag : ℕ) → k <ᵇ' triangular (suc diag) ≡ true
                   → findDiagonal (suc fuel) k diag ≡ diag
findDiagonal-found fuel k diag p with k <ᵇ' triangular (suc diag) | p
... | true | _ = refl
... | false | q = ex-falso (false≢true q)

findDiagonal-continue : (fuel k diag : ℕ) → k <ᵇ' triangular (suc diag) ≡ false
                      → findDiagonal (suc fuel) k diag ≡ findDiagonal fuel k (suc diag)
findDiagonal-continue fuel k diag p with k <ᵇ' triangular (suc diag) | p
... | false | _ = refl
... | true | q = ex-falso (true≢false q)

findDiagonal-aux : (w k acc fuel : ℕ) → w ∸ acc ≤ fuel
                 → k <ᵇ' triangular (suc w) ≡ true
                 → triangular w ≤ k
                 → acc ≤ w
                 → findDiagonal (suc fuel) k acc ≡ w
findDiagonal-aux w k acc zero w∸acc≤0 k<Tsw Tw≤k acc≤w with w ≟ acc
... | lt w<acc = ex-falso (¬m<m (≤-trans w<acc acc≤w))
... | eq w≡acc = subst (findDiagonal 1 k acc ≡_) (sym w≡acc) (findDiagonal-found 0 k acc (subst (λ x → k <ᵇ' triangular (suc x) ≡ true) w≡acc k<Tsw))
... | gt acc<w = ex-falso (¬m<m (≤-trans (∸-<-from w acc acc<w) w∸acc≤0))
  where
  ∸-<-from : (a b : ℕ) → b < a → 1 ≤ a ∸ b
  ∸-<-from zero zero 1≤0 = ex-falso (¬-<-zero 1≤0)
  ∸-<-from zero (suc b) sb<0 = ex-falso (¬-<-zero sb<0)
  ∸-<-from (suc a) zero _ = suc-≤-suc zero-≤
  ∸-<-from (suc a) (suc b) sb<sa = ∸-<-from a b (pred-≤-pred sb<sa)

findDiagonal-aux w k acc (suc fuel) w∸acc≤sf k<Tsw Tw≤k acc≤w with w ≟ acc
... | lt w<acc = ex-falso (¬m<m (≤-trans w<acc acc≤w))
... | eq w≡acc = subst (findDiagonal (suc (suc fuel)) k acc ≡_) (sym w≡acc) (findDiagonal-found (suc fuel) k acc (subst (λ x → k <ᵇ' triangular (suc x) ≡ true) w≡acc k<Tsw))
... | gt acc<w =
  let step1 = findDiagonal-continue (suc fuel) k acc (k≮ᵇ'triangular-suc-acc k w acc acc<w Tw≤k)
      step2 = findDiagonal-aux w k (suc acc) fuel (≤-pred-∸' w acc acc<w w∸acc≤sf) k<Tsw Tw≤k acc<w
  in step1 ∙ step2
  where
  ≤-pred-∸' : (w acc : ℕ) → acc < w → w ∸ acc ≤ suc fuel → w ∸ suc acc ≤ fuel
  ≤-pred-∸' zero acc 0<acc _ = ex-falso (¬-<-zero 0<acc)
  ≤-pred-∸' (suc w') acc acc<sw w∸acc≤sf = ≤-pred-∸-aux w' acc acc<sw w∸acc≤sf
    where
    ≤-pred-∸-aux : (w acc : ℕ) → acc < suc w → suc w ∸ acc ≤ suc fuel → suc w ∸ suc acc ≤ fuel
    ≤-pred-∸-aux w zero _ sw∸0≤sf = pred-≤-pred sw∸0≤sf
    ≤-pred-∸-aux w (suc acc) sacc<sw p = ≤-pred-∸-aux' w acc (pred-≤-pred sacc<sw) p
      where
      ≤-pred-∸-aux' : (w acc : ℕ) → acc < w → w ∸ acc ≤ suc fuel → w ∸ suc acc ≤ fuel
      ≤-pred-∸-aux' zero acc 1≤0 _ = ex-falso (¬-<-zero 1≤0)
      ≤-pred-∸-aux' (suc w') acc acc<sw' w∸acc≤sf' = ≤-pred-∸-aux w' acc acc<sw' w∸acc≤sf'

w≤cantorPair : (m n : ℕ) → m +ℕ n ≤ cantorPair m n
w≤cantorPair m n = ≤-trans (m+n≤tri-m+n m n) (≤-+k-r (triangular (m +ℕ n)) n)
  where
  n≤triangular-n : (n : ℕ) → n ≤ triangular n
  n≤triangular-n zero = zero-≤
  n≤triangular-n (suc n) = suc-≤-suc (≤-trans (n≤triangular-n n) (≤-+k-r' (triangular n) n))
    where
    ≤-+k-r' : (a b : ℕ) → a ≤ b +ℕ a
    ≤-+k-r' a zero = ≤-refl
    ≤-+k-r' a (suc b) = ≤-trans (≤-+k-r' a b) ≤-sucℕ

  m+n≤tri-m+n : (m n : ℕ) → m +ℕ n ≤ triangular (m +ℕ n)
  m+n≤tri-m+n m n = n≤triangular-n (m +ℕ n)

  ≤-+k-r : (a b : ℕ) → a ≤ a +ℕ b
  ≤-+k-r a zero = subst (a ≤_) (sym (+-zero a)) ≤-refl
  ≤-+k-r a (suc b) = subst (a ≤_) (sym (+-suc a b)) (≤-trans (≤-+k-r a b) ≤-sucℕ)

findDiagonal-correct : (m n : ℕ) →
  findDiagonal (suc (cantorPair m n)) (cantorPair m n) 0 ≡ m +ℕ n
findDiagonal-correct m n =
  let k = cantorPair m n
      w = m +ℕ n
  in findDiagonal-aux w k 0 k
       (w≤cantorPair m n)
       (cantorPair<ᵇ'-triangular-suc m n)
       (triangular≤cantorPair m n)
       zero-≤

cantorUnpair-pair : (m n : ℕ) → cantorUnpair (cantorPair m n) ≡ (m , n)
cantorUnpair-pair m n =
  let k = cantorPair m n
      w = m +ℕ n
      findW = findDiagonal-correct m n
  in
  cantorUnpair k
    ≡⟨ cong (λ w' → ((w' ∸ (k ∸ triangular w')) , (k ∸ triangular w'))) findW ⟩
  (w ∸ (k ∸ triangular w) , k ∸ triangular w)
    ≡⟨ cong (λ x → (w ∸ x , x)) (cantorPair-triangular-diff m n) ⟩
  (w ∸ n , n)
    ≡⟨ cong (λ x → (x , n)) (m+n∸n≡m m n) ⟩
  (m , n) ∎

a+b∸a≡b : (a b : ℕ) → a ≤ b → a +ℕ (b ∸ a) ≡ b
a+b∸a≡b zero b _ = refl
a+b∸a≡b (suc a) zero sa≤0 = ex-falso (¬-<-zero sa≤0)
a+b∸a≡b (suc a) (suc b) sa≤sb = cong suc (a+b∸a≡b a b (pred-≤-pred sa≤sb))

w∸n+n≡w : (w n : ℕ) → n ≤ w → (w ∸ n) +ℕ n ≡ w
w∸n+n≡w w n n≤w = ∸+-cancel w n n≤w

n≤w-from-bounds : (k w : ℕ) → triangular w ≤ k → k < triangular (suc w)
                → k ∸ triangular w ≤ w
n≤w-from-bounds k w Tw≤k k<Tsw =
  let step1 : k ∸ triangular w < triangular (suc w) ∸ triangular w
      step1 = ∸-mono-< k (triangular w) (triangular (suc w)) Tw≤k k<Tsw (triangular-suc w)
      eq : triangular (suc w) ∸ triangular w ≡ suc w
      eq = +∸-cancel (suc w) (triangular w)
      step2 : k ∸ triangular w < suc w
      step2 = subst (k ∸ triangular w <_) eq step1
  in pred-≤-pred step2
  where
  ∸-mono-< : (a b c : ℕ) → b ≤ a → a < c → b < c → a ∸ b < c ∸ b
  ∸-mono-< a b zero b≤a a<0 _ = ex-falso (¬-<-zero a<0)
  ∸-mono-< a b (suc c) b≤a sa≤sc b<sc with ≤Dec b a
  ... | yes b≤a' = subst (suc (a ∸ b) ≤_) (sym (suc-∸ c b (pred-≤-pred b<sc))) (suc-≤-suc (∸-mono a c b (pred-≤-pred sa≤sc) b≤a'))
    where
    suc-∸ : (x y : ℕ) → y ≤ x → suc x ∸ y ≡ suc (x ∸ y)
    suc-∸ x zero _ = refl
    suc-∸ (suc x) (suc y) sy≤sx = suc-∸ x y (pred-≤-pred sy≤sx)
    suc-∸ zero (suc y) sy≤0 = ex-falso (¬-<-zero sy≤0)

    ∸-mono : (x y z : ℕ) → x ≤ y → z ≤ x → x ∸ z ≤ y ∸ z
    ∸-mono x y zero x≤y _ = x≤y
    ∸-mono zero zero (suc z) _ sz≤0 = ex-falso (¬-<-zero sz≤0)
    ∸-mono zero (suc y) (suc z) _ sz≤0 = ex-falso (¬-<-zero sz≤0)
    ∸-mono (suc x) zero (suc z) sx≤0 _ = ex-falso (¬-<-zero sx≤0)
    ∸-mono (suc x) (suc y) (suc z) sx≤sy sz≤sx = ∸-mono x y z (pred-≤-pred sx≤sy) (pred-≤-pred sz≤sx)
  ... | no ¬b≤a = ex-falso (¬b≤a b≤a)

findDiagonal-lower-bound : (fuel k diag : ℕ) → triangular diag ≤ k
                         → triangular (findDiagonal fuel k diag) ≤ k
findDiagonal-lower-bound zero k diag Td≤k = Td≤k
findDiagonal-lower-bound (suc fuel) k diag Td≤k with k <ᵇ' triangular (suc diag) | inspect (k <ᵇ'_) (triangular (suc diag))
... | true | _ = Td≤k
... | false | [ p ] = findDiagonal-lower-bound fuel k (suc diag) (¬<ᵇ'-reflects k (triangular (suc diag)) p)

findDiagonal-upper-bound : (fuel k diag : ℕ) → suc k ≤ diag +ℕ fuel
                         → k < triangular (suc (findDiagonal fuel k diag))
findDiagonal-upper-bound zero k diag sk≤d0 =
  let sk≤d : suc k ≤ diag
      sk≤d = subst (suc k ≤_) (+-zero diag) sk≤d0
      sk≤sd : suc k ≤ suc diag
      sk≤sd = ≤-trans sk≤d ≤-sucℕ
      sd≤Tsd : suc diag ≤ triangular (suc diag)
      sd≤Tsd = n≤n+m (suc diag) (triangular diag)
  in ≤-trans sk≤sd sd≤Tsd
  where
  n≤n+m : (n m : ℕ) → n ≤ n +ℕ m
  n≤n+m n zero = subst (n ≤_) (sym (+-zero n)) ≤-refl
  n≤n+m n (suc m) = subst (n ≤_) (sym (+-suc n m)) (≤-trans (n≤n+m n m) ≤-sucℕ)
findDiagonal-upper-bound (suc fuel) k diag sk≤df with k <ᵇ' triangular (suc diag) | inspect (k <ᵇ'_) (triangular (suc diag))
... | true | [ p ] = <ᵇ'-reflects k (triangular (suc diag)) p
... | false | _ = findDiagonal-upper-bound fuel k (suc diag) (subst (suc k ≤_) (+-suc diag fuel) sk≤df)

findDiagonal-bounds : (k : ℕ) →
  let w = findDiagonal (suc k) k 0
  in (triangular w ≤ k) × (k < triangular (suc w))
findDiagonal-bounds k =
  let Tw≤k = findDiagonal-lower-bound (suc k) k 0 zero-≤
      k<Tsw = findDiagonal-upper-bound (suc k) k 0 ≤-refl
  in Tw≤k , k<Tsw

cantorPair-unpair : (k : ℕ) → uncurry cantorPair (cantorUnpair k) ≡ k
cantorPair-unpair k =
  let w = findDiagonal (suc k) k 0
      n' = k ∸ triangular w
      m' = w ∸ n'
      (Tw≤k , k<Tsw) = findDiagonal-bounds k
      n'≤w = n≤w-from-bounds k w Tw≤k k<Tsw
      m'+n'=w : m' +ℕ n' ≡ w
      m'+n'=w = w∸n+n≡w w n' n'≤w
      step1 : cantorPair m' n' ≡ triangular (m' +ℕ n') +ℕ n'
      step1 = refl
      step2 : triangular (m' +ℕ n') +ℕ n' ≡ triangular w +ℕ n'
      step2 = cong (λ x → triangular x +ℕ n') m'+n'=w
      step3 : triangular w +ℕ n' ≡ k
      step3 = a+b∸a≡b (triangular w) k Tw≤k
  in
  uncurry cantorPair (cantorUnpair k)
    ≡⟨ refl ⟩
  cantorPair m' n'
    ≡⟨ step1 ⟩
  triangular (m' +ℕ n') +ℕ n'
    ≡⟨ step2 ⟩
  triangular w +ℕ n'
    ≡⟨ step3 ⟩
  k ∎

-- =============================================================================
-- Open propositions are closed under finite conjunction (lines 2391-2443)
-- =============================================================================

openAnd : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
        → isOpenProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
openAnd P Q (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) = γ , forward , backward
  where
  γ : binarySequence
  γ k = let (n , m) = cantorUnpair k in α n and β m

  forward : ⟨ P ⟩ × ⟨ Q ⟩ → Σ[ k ∈ ℕ ] γ k ≡ true
  forward (p , q) =
    let (n , αn=t) = P→∃α p
        (m , βm=t) = Q→∃β q
        k = cantorPair n m
        γk=t : γ k ≡ true
        γk=t =
          γ k
            ≡⟨ cong (λ p → α (fst p) and β (snd p)) (cantorUnpair-pair n m) ⟩
          α n and β m
            ≡⟨ cong (λ x → x and β m) αn=t ⟩
          true and β m
            ≡⟨ cong (true and_) βm=t ⟩
          true ∎
    in (k , γk=t)

  backward : Σ[ k ∈ ℕ ] γ k ≡ true → ⟨ P ⟩ × ⟨ Q ⟩
  backward (k , γk=t) =
    let (n , m) = cantorUnpair k
        αn∧βm=t : α n and β m ≡ true
        αn∧βm=t = γk=t
        αn=t : α n ≡ true
        αn=t = and-true-left (α n) (β m) αn∧βm=t
        βm=t : β m ≡ true
        βm=t = and-true-right (α n) (β m) αn∧βm=t
    in (∃α→P (n , αn=t)) , (∃β→Q (m , βm=t))
    where
    and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
    and-true-left true true _ = refl
    and-true-left true false p = ex-falso (false≢true p)
    and-true-left false true p = ex-falso (false≢true p)
    and-true-left false false p = ex-falso (false≢true p)

    and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
    and-true-right true true _ = refl
    and-true-right true false p = ex-falso (false≢true p)
    and-true-right false true p = ex-falso (false≢true p)
    and-true-right false false p = ex-falso (false≢true p)

-- Bundled version: meet (∧) on Open
_∧-Open_ : Open → Open → Open
O₁ ∧-Open O₂ = ((⟨ fst O₁ ⟩ × ⟨ fst O₂ ⟩) , isProp× (snd (fst O₁)) (snd (fst O₂))) ,
               openAnd (fst O₁) (fst O₂) (snd O₁) (snd O₂)

-- Bundled version: meet (∧) on Closed
_∧-Closed_ : Closed → Closed → Closed
C₁ ∧-Closed C₂ = ((⟨ fst C₁ ⟩ × ⟨ fst C₂ ⟩) , isProp× (snd (fst C₁)) (snd (fst C₂))) ,
                 closedAnd (fst C₁) (fst C₂) (snd C₁) (snd C₂)

-- =============================================================================
-- Closed propositions are closed under disjunction (uses LLPO)
-- =============================================================================

-- First-true truncation: given a sequence, produce one that hits true at most once
firstTrue : binarySequence → binarySequence
firstTrue α zero = α zero
firstTrue α (suc n) with α zero
... | true = false
... | false = firstTrue (α ∘ suc) n

-- firstTrue preserves never-hitting-true
firstTrue-preserves-allFalse : (α : binarySequence) → ((n : ℕ) → α n ≡ false)
                             → (n : ℕ) → firstTrue α n ≡ false
firstTrue-preserves-allFalse α allF zero = allF zero
firstTrue-preserves-allFalse α allF (suc n) with α zero | allF zero
... | true  | α0=f = ex-falso (false≢true (sym α0=f))
... | false | _    = firstTrue-preserves-allFalse (α ∘ suc) (allF ∘ suc) n

-- firstTrue sequence hits true at most once
firstTrue-hitsAtMostOnce : (α : binarySequence) → hitsAtMostOnce (firstTrue α)
firstTrue-hitsAtMostOnce α m n ftm=t ftn=t = aux α m n ftm=t ftn=t
  where
  aux : (α : binarySequence) → (m n : ℕ) → firstTrue α m ≡ true → firstTrue α n ≡ true → m ≡ n
  aux α zero zero _ _ = refl
  aux α zero (suc n) ft0=t ft-sn=t with α zero
  aux α zero (suc n) ft0=t ft-sn=t | true = ex-falso (false≢true ft-sn=t)
  aux α zero (suc n) ft0=t ft-sn=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) zero ft-sm=t ft0=t with α zero
  aux α (suc m) zero ft-sm=t ft0=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) zero ft-sm=t ft0=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t with α zero
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | false = cong suc (aux (α ∘ suc) m n ft-sm=t ft-sn=t)

-- Key lemma: firstTrue α n = true implies α n = true
firstTrue-true-implies-original-true : (α : binarySequence) (n : ℕ)
                                      → firstTrue α n ≡ true → α n ≡ true
firstTrue-true-implies-original-true α zero ft0=t = ft0=t
firstTrue-true-implies-original-true α (suc n) ft-sn=t with α zero
... | true  = ex-falso (false≢true ft-sn=t)
... | false = firstTrue-true-implies-original-true (α ∘ suc) n ft-sn=t

-- Helper for firstTrue with explicit evidence
private
  firstTrue-with : (α : binarySequence) (n : ℕ) (b : Bool)
                  → α zero ≡ b
                  → firstTrue α (suc n) ≡ (if b then false else firstTrue (α ∘ suc) n)
  firstTrue-with α n true  p with α zero
  ... | true = refl
  ... | false = ex-falso (true≢false (sym p))
  firstTrue-with α n false p with α zero
  ... | true = ex-falso (false≢true (sym p))
  ... | false = refl

firstTrue-false-but-original-true : (α : binarySequence) (n : ℕ)
                                   → firstTrue α n ≡ false → α n ≡ true
                                   → Σ[ m ∈ ℕ ] (suc m ≤ n) × (α m ≡ true)
firstTrue-false-but-original-true α zero ft0=f α0=t = ex-falso (true≢false (sym α0=t ∙ ft0=f))
firstTrue-false-but-original-true α (suc n) ft-sn=f α-sn=t with α zero =B true
... | yes α0=t = zero , suc-≤-suc zero-≤ , α0=t
... | no α0≠t =
  let α0=f = ¬true→false (α zero) α0≠t
      eq : firstTrue α (suc n) ≡ firstTrue (α ∘ suc) n
      eq = firstTrue-with α n false α0=f ∙ refl
      ft-sn=f' : firstTrue (α ∘ suc) n ≡ false
      ft-sn=f' = sym eq ∙ ft-sn=f
      (m , m<n , αsm=t) = firstTrue-false-but-original-true (α ∘ suc) n ft-sn=f' α-sn=t
  in suc m , suc-≤-suc m<n , αsm=t

-- De Morgan law for closed propositions (consequence of LLPO)
closedDeMorgan : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
               → ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
closedDeMorgan P Q (α , P→∀α , ∀α→P) (β , Q→∀β , ∀β→Q) ¬¬P∧¬Q =
  let δ₀ : binarySequence
      δ₀ = interleave α β

      δ : binarySequence
      δ = firstTrue δ₀

      δ-hamo : hitsAtMostOnce δ
      δ-hamo = firstTrue-hitsAtMostOnce δ₀

      δ∞ : ℕ∞
      δ∞ = δ , δ-hamo

      llpo-result : ((k : ℕ) → δ (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → δ (suc (2 ·ℕ k)) ≡ false)
      llpo-result = llpo δ∞

  in helper llpo-result
  where
  module _ where
    open WF.WFI (<-wellfounded)

    ResultOdd : ℕ → Type₀
    ResultOdd n = interleave α β n ≡ true
                → ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false)
                → Σ[ m ∈ ℕ ] (isEvenB m ≡ false) × (β (half m) ≡ true)

    find-first-true-odd-step : (n : ℕ) → ((m : ℕ) → m < n → ResultOdd m) → ResultOdd n
    find-first-true-odd-step n rec δ₀-n=t allEvensF with firstTrue (interleave α β) n =B true
    ... | yes ft-n=t with isEvenB n =B true
    ...   | yes n-even =
            let k = half n
                2k=n : 2 ·ℕ k ≡ n
                2k=n = 2·half-even n n-even
            in ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true) (sym 2k=n) ft-n=t)
                                     ∙ allEvensF k))
    ...   | no n-odd =
            let j = half n
                m-odd-eq : isEvenB n ≡ false
                m-odd-eq = ¬true→false (isEvenB n) n-odd
                βj=t : β j ≡ true
                βj=t = sym (interleave-odd α β n m-odd-eq) ∙ δ₀-n=t
            in n , m-odd-eq , βj=t
    find-first-true-odd-step n rec δ₀-n=t allEvensF | no ft-n≠t =
      let ft-n=f = ¬true→false (firstTrue (interleave α β) n) ft-n≠t
          (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n ft-n=f δ₀-n=t
      in rec m m<n δ₀-m=t allEvensF

    find-first-true-odd : (n : ℕ) → ResultOdd n
    find-first-true-odd = induction find-first-true-odd-step

  allEvensF-implies-P : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false) → ⟨ P ⟩
  allEvensF-implies-P allEvensF = closedIsStable P (α , P→∀α , ∀α→P) ¬¬P
    where
    ¬¬P : ¬ ¬ ⟨ P ⟩
    ¬¬P ¬p =
      let (k , αk=t) = mp α (λ all-false → ¬p (∀α→P all-false))
          δ₀-2k=t : interleave α β (2 ·ℕ k) ≡ true
          δ₀-2k=t = interleave-2k α β k ∙ αk=t
          (m , m-odd , βj=t) = find-first-true-odd (2 ·ℕ k) δ₀-2k=t allEvensF
          j = half m
          ¬q : ¬ ⟨ Q ⟩
          ¬q q = false≢true (sym (Q→∀β q j) ∙ βj=t)
      in ¬¬P∧¬Q (¬p , ¬q)

  module _ where
    open WF.WFI (<-wellfounded)

    ResultEven : ℕ → Type₀
    ResultEven n = interleave α β n ≡ true
                 → ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false)
                 → Σ[ m ∈ ℕ ] (isEvenB m ≡ true) × (α (half m) ≡ true)

    find-first-true-even-step : (n : ℕ) → ((m : ℕ) → m < n → ResultEven m) → ResultEven n
    find-first-true-even-step n rec δ₀-n=t allOddsF with firstTrue (interleave α β) n =B true
    ... | yes ft-n=t with isEvenB n =B true
    ...   | yes n-even =
            let j = half n
                αj=t : α j ≡ true
                αj=t = sym (interleave-even α β n n-even) ∙ δ₀-n=t
            in n , n-even , αj=t
    ...   | no n-odd =
            let k = half n
                n-odd-eq : isEvenB n ≡ false
                n-odd-eq = ¬true→false (isEvenB n) n-odd
                2k+1=n : suc (2 ·ℕ k) ≡ n
                2k+1=n = suc-2·half-odd n n-odd-eq
            in ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true) (sym 2k+1=n) ft-n=t)
                                     ∙ allOddsF k))
    find-first-true-even-step n rec δ₀-n=t allOddsF | no ft-n≠t =
      let ft-n=f = ¬true→false (firstTrue (interleave α β) n) ft-n≠t
          (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n ft-n=f δ₀-n=t
      in rec m m<n δ₀-m=t allOddsF

    find-first-true-even : (n : ℕ) → ResultEven n
    find-first-true-even = induction find-first-true-even-step

  allOddsF-implies-Q : ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false) → ⟨ Q ⟩
  allOddsF-implies-Q allOddsF = closedIsStable Q (β , Q→∀β , ∀β→Q) ¬¬Q
    where
    ¬¬Q : ¬ ¬ ⟨ Q ⟩
    ¬¬Q ¬q =
      let (k , βk=t) = mp β (λ all-false → ¬q (∀β→Q all-false))
          δ₀-odd-k=t : interleave α β (suc (2 ·ℕ k)) ≡ true
          δ₀-odd-k=t = interleave-2k+1 α β k ∙ βk=t
          (m , m-even , αj=t) = find-first-true-even (suc (2 ·ℕ k)) δ₀-odd-k=t allOddsF
          j = half m
          ¬p : ¬ ⟨ P ⟩
          ¬p p = false≢true (sym (P→∀α p j) ∙ αj=t)
      in ¬¬P∧¬Q (¬p , ¬q)

  helper : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false)
         ⊎ ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false)
         → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
  helper (inl allEvensF) = ∣ inl (allEvensF-implies-P allEvensF) ∣₁
  helper (inr allOddsF) = ∣ inr (allOddsF-implies-Q allOddsF) ∣₁

-- Now we can define closedOr
closedOr : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
         → isClosedProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
closedOr P Q Pclosed Qclosed = γ , forward , backward
  where
  ¬P : hProp ℓ-zero
  ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

  ¬Q : hProp ℓ-zero
  ¬Q = (¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩

  ¬Popen : isOpenProp ¬P
  ¬Popen = negClosedIsOpen mp P Pclosed

  ¬Qopen : isOpenProp ¬Q
  ¬Qopen = negClosedIsOpen mp Q Qclosed

  ¬P∧¬Q : hProp ℓ-zero
  ¬P∧¬Q = ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) , isProp× (isProp¬ ⟨ P ⟩) (isProp¬ ⟨ Q ⟩)

  ¬P∧¬Qopen : isOpenProp ¬P∧¬Q
  ¬P∧¬Qopen = openAnd ¬P ¬Q ¬Popen ¬Qopen

  γ : binarySequence
  γ = fst ¬P∧¬Qopen

  forward : ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ → (n : ℕ) → γ n ≡ false
  forward P∨Q n with γ n =B true
  ... | yes γn=t = ex-falso (PT.rec isProp⊥ (helper' γn=t) P∨Q)
    where
    helper' : γ n ≡ true → ⟨ P ⟩ ⊎ ⟨ Q ⟩ → ⊥
    helper' γn=t (inl p) = fst (snd (snd ¬P∧¬Qopen) (n , γn=t)) p
    helper' γn=t (inr q) = snd (snd (snd ¬P∧¬Qopen) (n , γn=t)) q
  ... | no γn≠t = ¬true→false (γ n) γn≠t

  backward : ((n : ℕ) → γ n ≡ false) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
  backward all-false =
    let ¬¬P∧¬Q : ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩))
        ¬¬P∧¬Q (¬p , ¬q) =
          let (n , γn=t) = fst (snd ¬P∧¬Qopen) (¬p , ¬q)
          in false≢true (sym (all-false n) ∙ γn=t)
    in closedDeMorgan P Q Pclosed Qclosed ¬¬P∧¬Q

-- Bundled version: join (∨) on Open
_∨-Open_ : Open → Open → Open
O₁ ∨-Open O₂ = ((∥ ⟨ fst O₁ ⟩ ⊎ ⟨ fst O₂ ⟩ ∥₁) , squash₁) ,
               openOr (fst O₁) (fst O₂) (snd O₁) (snd O₂)

-- Bundled version: join (∨) on Closed
_∨-Closed_ : Closed → Closed → Closed
C₁ ∨-Closed C₂ = ((∥ ⟨ fst C₁ ⟩ ⊎ ⟨ fst C₂ ⟩ ∥₁) , squash₁) ,
                 closedOr (fst C₁) (fst C₂) (snd C₁) (snd C₂)

-- De Morgan for open propositions
openDeMorgan : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
             → (¬ (⟨ P ⟩ × ⟨ Q ⟩)) ↔ ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
openDeMorgan P Q Popen Qopen = forward , backward
  where
  ¬Pclosed : isClosedProp (¬hProp P)
  ¬Pclosed = negOpenIsClosed P Popen

  ¬Qclosed : isClosedProp (¬hProp Q)
  ¬Qclosed = negOpenIsClosed Q Qopen

  forward : ¬ (⟨ P ⟩ × ⟨ Q ⟩) → ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
  forward ¬P×Q = closedDeMorgan (¬hProp P) (¬hProp Q) ¬Pclosed ¬Qclosed ¬¬¬P×¬¬Q
    where
    Pstable : ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
    Pstable = openIsStable mp P Popen

    Qstable : ¬ ¬ ⟨ Q ⟩ → ⟨ Q ⟩
    Qstable = openIsStable mp Q Qopen

    ¬¬¬P×¬¬Q : ¬ ((¬ ¬ ⟨ P ⟩) × (¬ ¬ ⟨ Q ⟩))
    ¬¬¬P×¬¬Q (¬¬p , ¬¬q) = ¬P×Q (Pstable ¬¬p , Qstable ¬¬q)

  backward : ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁ → ¬ (⟨ P ⟩ × ⟨ Q ⟩)
  backward = PT.rec (isProp¬ _) λ { (inl ¬p) (p , _) → ¬p p
                                   ; (inr ¬q) (_ , q) → ¬q q }

