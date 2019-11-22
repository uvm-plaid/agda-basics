{-# OPTIONS --type-in-type #-}

module Basics002 where

infixl 1 [AT]

infixr 2 CASE_OF_

infixr 3 existential

infixr 4 _$_

infixl 5 _∨_
infixl 6 _∧_
infixr 7 ¬_
infix 8 _≡_
infix 8 _<_
infix 8 _≤_
infix 8 _<⋆!_
infix 8 _≤⋆!_
infix 8 _⋚⋆!_
infix 8 _≤[first]_
infix 8 _≤[all]_
infix 8 _∈_

infix 15 _≫=[list]_

infixr 20 _∷_
infix 24 _≡?_
infix 24 _<?_
infix 24 _≤?_
infix 24 _⋚?_
infixl 25 _+_
infixl 25 _+ᶻ_
infixl 25 _+ʳ_
infixl 25 _⧺_
infixl 25 _⧻_
infixl 26 _×_
infixl 26 _×ᶻ_
infixl 26 _×ʳ_
infixl 26 _/ʳ_
infixl 26 _⋅_
infixl 27 _⋈[≤]_
infixl 27 _¬◇[<]_
infixl 28 _∘_
infixl 28 _⊚[≡]_
infixl 28 _⊚[≤]_
infixl 28 _⊚[<]_
infixl 28 _⊚[≤/<]_
infixl 28 _⊚[</≤]_
infixr 29 _^ʳ_
infixr 30 ⁻ʳ_

-- ====== --
-- SYNTAX --
-- ====== --

syntax [AT] A x = x AT A
[AT] : ∀ (A : Set) → A → A
[AT] A x = x

-- ========= --
-- FUNCTIONS -- 
-- ========= --

id : ∀ {A : Set} → A → A
id x = x

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_$_ : ∀ {A B : Set} → (A → B) → A → B
f $ x = f x

CASE_OF_ : ∀ {A B : Set} → A → (A → B) → B
CASE x OF f = f x

-- ===== --
-- EMPTY --
-- ===== --

data 𝟘 : Set where

¬_ : Set → Set
¬ A = A → 𝟘

-- ==== --
-- UNIT --
-- ==== --

record 𝟙 : Set where
  instance
    constructor •
{-# BUILTIN UNIT 𝟙 #-}
{-# COMPILE GHC 𝟙 = data () (()) #-}

-- ============== --
-- DISJOINT UNION --
-- ============== --

data _∨_ (A B : Set) : Set where
  Inl : A → A ∨ B
  Inr : B → A ∨ B

-- ==== --
-- PAIR --
-- ==== --

record _∧_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    π₁ : A
    π₂ : B
open _∧_ public

-- ============== --
-- DEPENDENT PAIR --
-- ============== --

syntax existential A (λ x → B) = ∃ x ⦂ A ST B
data existential (A : Set) (B : A → Set) : Set where
  ⟨∃_,_⟩ : ∀ (x : A) → B x → existential A B

-- ======== --
-- BOOLEANS --
-- ======== --

data 𝔹 : Set where
  I : 𝔹
  O : 𝔹
{-# BUILTIN BOOL  𝔹 #-}
{-# BUILTIN TRUE  I #-}
{-# BUILTIN FALSE O #-}

_⩓_ : 𝔹 → 𝔹 → 𝔹
O ⩓ _ = O
_ ⩓ O = O
I ⩓ I = I

_⩔_ : 𝔹 → 𝔹 → 𝔹
I ⩔ _ = I
_ ⩔ I = I
O ⩔ O = O

not : 𝔹 → 𝔹
not I = O
not O = I

_⊕_ : 𝔹 → 𝔹 → 𝔹
I ⊕ I = O
I ⊕ O = I
O ⊕ I = O
O ⊕ O = O

-- ======== --
-- EQUALITY --
-- ======== --

data _≡_ {A : Set} (x : A) : A → Set where
  instance
    ↯ : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

postulate
  _⊚[≡]_ : ∀ {A} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
  ◇[≡] : ∀ {A} {x y : A} → x ≡ y → y ≡ x

-- ======== --
-- NATURALS --
-- ======== --

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
Z    + n  =  n
(S m) + n  =  S (m + n)

_×_ : ℕ → ℕ → ℕ
Z × _ = Z
S m × n = n + m × n

postulate
  lunit[+] : ∀ (m : ℕ) → 0 + m ≡ m
  runit[+] : ∀ (m : ℕ) → m + 0 ≡ m
  assoc[+] : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
  commu[+] : ∀ (m n : ℕ) → m + n ≡ n + m

  lunit[×] : ∀ (m : ℕ) → 1 × m ≡ m
  runit[×] : ∀ (m : ℕ) → m × 1 ≡ m
  lzero[×] : ∀ (m : ℕ) → 0 × m ≡ 0
  rzero[×] : ∀ (m : ℕ) → m × 0 ≡ 0
  assoc[×] : ∀ (m n p : ℕ) → m × (n × p) ≡ (m × n) × p
  commu[×] : ∀ (m n : ℕ) → m × n ≡ n × m
  ldist[×] : ∀ (m n p : ℕ) → m × (n + p) ≡ m × n + m × p
  rdist[×] : ∀ (m n p : ℕ) → (m + n) × p ≡ m × p + n × p

-----------
-- order --
-----------

data ≡! : Set where
  [≡] : ≡!
  [≢] : ≡!

data <! : Set where
  [<] : <!
  [≥] : <!

data ≤! : Set where
  [≤] : ≤!
  [>] : ≤!

data ⋚! : Set where
  [<] : ⋚!
  [≡] : ⋚!
  [>] : ⋚!

_≡?_ : ℕ → ℕ → 𝔹
Z ≡? Z = I
Z ≡? S n = O
S m ≡? Z = O
S m ≡? S n = m ≡? n

_<?_ : ℕ → ℕ → <!
_ <? Z = [≥]
Z <? S n = [<]
S m <? S n = m <? n

_≤?_ : ℕ → ℕ → ≤!
Z ≤? n = [≤]
S m ≤? Z = [>]
S m ≤? S n = m ≤? n

_⋚?_ : ℕ → ℕ → ⋚!
Z ⋚? Z = [≡]
Z ⋚? S n = [<]
S m ⋚? Z = [>]
S m ⋚? S n = m ⋚? n

data _≡⋆!_ (m n : ℕ) : Set where
  [≡] : m ≡ n → m ≡⋆! n
  [≢] : ¬ m ≡ n → m ≡⋆! n

data _<_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z < S n
  S : ∀ {m n} → m < n → S m < S n

data _≤_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z ≤ n
  S : ∀ {m n} → m ≤ n → S m ≤ S n

data _<⋆!_ (m n : ℕ) : Set where
  [<] : m < n → m <⋆! n
  [≥] : n ≤ m → m <⋆! n

data _≤⋆!_ (m n : ℕ) : Set where
  [≤] : m ≤ n → m ≤⋆! n
  [>] : n < m → m ≤⋆! n

data _⋚⋆!_ (m n : ℕ) : Set where
  [<] : m < n → m ⋚⋆! n
  [≡] : m ≡ n → m ⋚⋆! n
  [>] : n < m → m ⋚⋆! n

postulate
  xRx[≤] : ∀ (m : ℕ) → m ≤ m
  _⊚[≤]_ : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
  _⋈[≤]_ : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n

  ¬xRx[<] : ∀ {m : ℕ} → m < m → 𝟘
  _⊚[<]_ : ∀ {m n p : ℕ} → n < p → m < n → m < p
  _¬◇[<]_ : ∀ {m n : ℕ} → m < n → n < m → 𝟘

  _⊚[</≤]_ : ∀ {m n p : ℕ} → n < p → m ≤ n → m < p
  _⊚[≤/<]_ : ∀ {m n p : ℕ} → n ≤ p → m < n → m < p

  s[≤] : ∀ (m : ℕ) → m ≤ S m
  s[<] : ∀ (m : ℕ) → m < S m

  wk[<] : ∀ {m n : ℕ} → m < n → m ≤ n
  in[≤] : ∀ {m n : ℕ} → m ≤ n → m < n ∨ m ≡ n

  to[</≤] : ∀ {m n : ℕ} → m < n → S m ≤ n
  fr[</≤] : ∀ {m n : ℕ} → S m ≤ n → m < n

  to[≤/<] : ∀ {m n : ℕ} → m ≤ n → m < S n
  fr[≤/<] : ∀ {m n : ℕ} → m < S n → m ≤ n

  snd[<?/<] : ∀ {m n : ℕ} → m <? n ≡ [<] → m < n
  snd[<?/≥] : ∀ {m n : ℕ} → m <? n ≡ [≥] → n ≤ m

  cmp[<?/<] : ∀ {m n : ℕ} → m < n → m <? n ≡ [<]
  cmp[<?/≥] : ∀ {m n : ℕ} → n ≤ m → m <? n ≡ [≥]

  snd[≤?/≤] : ∀ {m n : ℕ} → m ≤? n ≡ [≤] → m ≤ n
  snd[≤?/>] : ∀ {m n : ℕ} → m ≤? n ≡ [>] → n < m

  cmp[≤?/≤] : ∀ {m n : ℕ} → m ≤ n → m ≤? n ≡ [≤]
  cmp[≤?/>] : ∀ {m n : ℕ} → n < m → m ≤? n ≡ [>]

  snd[⋚?/<] : ∀ {m n : ℕ} → m ⋚? n ≡ [<] → m < n
  snd[⋚?/≡] : ∀ {m n : ℕ} → m ⋚? n ≡ [≡] → m ≡ n
  snd[⋚?/>] : ∀ {m n : ℕ} → m ⋚? n ≡ [>] → n < m

  cmp[⋚?/<] : ∀ {m n : ℕ} → m < n → m ⋚? n ≡ [<]
  cmp[⋚?/≡] : ∀ {m n : ℕ} → m ≡ n → m ⋚? n ≡ [≡]
  cmp[⋚?/>] : ∀ {m n : ℕ} → n < m → m ⋚? n ≡ [>]

  _≤⋆_ : ∀ (m n : ℕ) → m ≤⋆! n
  _⋚⋆_ : ∀ (m n : ℕ) → m ⋚⋆! n

  lmono[+/≤] : ∀ (x x′ y : ℕ) → x ≤ x′ → x + y ≤ x′ + y
  rmono[+/≤] : ∀ (x y y′ : ℕ) → y ≤ y′ → x + y ≤ x + y′

  lmono[+/<] : ∀ (x x′ y : ℕ) → x < x′ → x + y < x′ + y
  rmono[+/<] : ∀ (x y y′ : ℕ) → y < y′ → x + y < x + y′

-- ======== --
-- INTEGERS --
-- ======== --

data ℤ : Set where
  Pos : ℕ → ℤ
  NegS : ℕ → ℤ
{-# BUILTIN INTEGER       ℤ    #-}
{-# BUILTIN INTEGERPOS    Pos  #-}
{-# BUILTIN INTEGERNEGSUC NegS #-}

_∸_ : ℕ → ℕ → ℤ
m ∸ Z = Pos m
Z ∸ S n = NegS n
S m ∸ S n = m ∸ n

_+ᶻ_ : ℤ → ℤ → ℤ
Pos m +ᶻ Pos n = Pos (m + n)
Pos m +ᶻ NegS n = m ∸ S n
NegS m +ᶻ Pos n = n ∸ S m
NegS m +ᶻ NegS n = NegS (S (m + n))

_×ᶻ_ : ℤ → ℤ → ℤ
Pos Z ×ᶻ _ = Pos Z
_ ×ᶻ Pos Z = Pos Z
Pos m ×ᶻ Pos n = Pos (m × n)
Pos (S m) ×ᶻ NegS n = NegS (m + n + (m × n))
NegS m ×ᶻ Pos (S n) = NegS (m + n + (m × n))
NegS m ×ᶻ NegS n = Pos (S m × S n)

postulate
  lunit[+ᶻ] : ∀ (m : ℤ) → Pos 0 +ᶻ m ≡ m
  runit[+ᶻ] : ∀ (m : ℤ) → m +ᶻ Pos 0 ≡ m
  assoc[+ᶻ] : ∀ (m n p : ℤ) → m +ᶻ (n +ᶻ p) ≡ (m +ᶻ n) +ᶻ p
  commu[+ᶻ] : ∀ (m n : ℤ) → m +ᶻ n ≡ n +ᶻ m

  lunit[×ᶻ] : ∀ (m : ℤ) → Pos 1 ×ᶻ m ≡ m
  runit[×ᶻ] : ∀ (m : ℤ) → m ×ᶻ Pos 1 ≡ m
  lzero[×ᶻ] : ∀ (m : ℤ) → Pos 0 ×ᶻ m ≡ Pos 0
  rzero[×ᶻ] : ∀ (m : ℤ) → m ×ᶻ Pos 0 ≡ Pos 0
  assoc[×ᶻ] : ∀ (m n p : ℤ) → m ×ᶻ (n ×ᶻ p) ≡ (m ×ᶻ n) ×ᶻ p
  commu[×ᶻ] : ∀ (m n : ℤ) → m ×ᶻ n ≡ n ×ᶻ m
  ldist[×ᶻ] : ∀ (m n p : ℤ) → m ×ᶻ (n +ᶻ p) ≡ m ×ᶻ n +ᶻ m ×ᶻ p
  rdist[×ᶻ] : ∀ (m n p : ℤ) → (m +ᶻ n) ×ᶻ p ≡ m ×ᶻ p +ᶻ n ×ᶻ p

-- ===== --
-- RATIO --
-- ===== --

record 𝕋 : Set where
  constructor _⫽ᵗ_
  field
    numᵗ : ℕ
    denᵗ : ℕ
open 𝕋 public

-- ======== --
-- RATIONAL --
-- ======== --

record ℚ : Set where
  constructor _⫽ᶝ_
  field
    numᶝ : ℤ
    denᶝ : ℕ
open ℚ public

-- ===== --
-- LISTS --
-- ===== --

data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A

{-# BUILTIN LIST list #-}

_⧺_ : ∀ {A : Set} → list A → list A → list A
[] ⧺ ys = ys
(x ∷ xs) ⧺ ys = x ∷ (xs ⧺ ys)

length : ∀ {A : Set} → list A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

map : ∀ {A B} → (A → B) → list A → list B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_⨳[_]_ : ∀ {A : Set} → list A → (A → A → A) → list A → list A
[] ⨳[ _⊞_ ] ys = []
(x ∷ xs) ⨳[ _⊞_ ] ys = map (λ y → x ⊞ y) ys ⧺ (xs ⨳[ _⊞_ ] ys)

return[list] : ∀ {A} → A → list A
return[list] x = x ∷ []

_≫=[list]_ : ∀ {A B : Set} → list A → (A → list B) → list B
[] ≫=[list] f = []
(x ∷ xs) ≫=[list] f = f x ⧺ (xs ≫=[list] f)

llfold : ∀ {A B : Set} → list A → B → (A → B → B) → B
llfold [] i f = i
llfold (x ∷ xs) i f = llfold xs (f x i) f

lrfold : ∀ {A B : Set} → list A → B → (A → B → B) → B
lrfold [] i f = i
lrfold (x ∷ xs) i f = f x (lrfold xs i f)

postulate
  lunit[⧺] : ∀ {A} (xs : list A) → [] ⧺ xs ≡ xs
  runit[⧺] : ∀ {A} (xs : list A) → xs ⧺ [] ≡ xs
  assoc[⧺] : ∀ {A} (xs ys zs : list A) → xs ⧺ (ys ⧺ zs) ≡ (xs ⧺ ys) ⧺ zs

  unit[map] : ∀ {A} (xs : list A) → map id xs ≡ xs
  homm[map] : ∀ {A B C} (g : B → C) (f : A → B) (xs : list A) → map (g ∘ f) xs ≡ map g (map f xs)

  lunit[⨳][_] : ∀ {A} (_⊞_ : A → A → A) (x : A) (xs : list A) → (x ∷ []) ⨳[ _⊞_ ] xs ≡ map (_⊞_ x) xs
  runit[⨳][_] : ∀ {A} (_⊞_ : A → A → A) (x : A) (xs : list A) → xs ⨳[ _⊞_ ] (x ∷ []) ≡ map (λ y → y ⊞ x) xs
  assoc[⨳][_] : ∀ {A} (_⊞_ : A → A → A) (xs ys zs : list A)
    → (∀ x y z → x ⊞ (y ⊞ z) ≡ (x ⊞ y) ⊞ z)
    → xs ⨳[ _⊞_ ] (ys ⨳[ _⊞_ ] zs) ≡ (xs ⨳[ _⊞_ ] ys) ⨳[ _⊞_ ] zs

  lunit[≫=][list] : ∀ {A B} (x : A) (f : A → list B) → return[list] x ≫=[list] f ≡ f x
  runit[≫=][list] : ∀ {A} (xs : list A) → xs ≫=[list] return[list] ≡ xs
  assoc[≫=][list] : ∀ {A B C} (xs : list A) (f : A → list B) (g : B → list C)
    → (xs ≫=[list] f) ≫=[list] g ≡ xs ≫=[list] (λ x → f x ≫=[list] g)

module monad-list where
  return = return[list]
  _>>=_ = _≫=[list]_
  _>>_ : ∀ {A B} → list A → list B → list B
  xM >> yM = xM ≫=[list] λ _ → yM
  lunit[≫=] = lunit[≫=][list]
  runit[≫=] = runit[≫=][list]

-----------
-- order --
-----------

data _≤[first]_ (m : ℕ) : list ℕ → Set where
  [] : m ≤[first] []
  ⟨_⟩ : ∀ {n ns}
    → m ≤ n
    → m ≤[first] n ∷ ns

data sorted : list ℕ → Set where
  [] : sorted []
  _∷_ : ∀ {x xs}
    → x ≤[first] xs
    → sorted xs
    → sorted (x ∷ xs)

data _≤[all]_ (x : ℕ) : list ℕ → Set where
  [] : x ≤[all] []
  _∷_  : ∀ {y : ℕ} {ys : list ℕ}
    → x ≤ y
    → x ≤[all] ys
    → x ≤[all] (y ∷ ys)

-- ============= --
-- ACCESSIBILITY --
-- ============= --

data acc (x : ℕ) : Set where
  Acc : (∀ {y} → y < x → acc y) → acc x

acc[<] : ∀ {m} (n : ℕ) → m < n → acc m
acc[<] Z ()
acc[<] (S n) Z = Acc λ where ()
acc[<] (S n) (S ε) = Acc λ where ε′ → (acc[<] n) ( to[</≤] ε ⊚[≤/<] ε′)

wf[<] : ∀ (n : ℕ) → acc n
wf[<] n = Acc (acc[<] n)

-- ======= --
-- VECTORS --
-- ======= --

data vec (A : Set) : ℕ → Set where
  [] : vec A Z
  _∷_ : ∀ {n} → A → vec A n → vec A (S n)

vec[_] : ℕ → Set → Set
vec[ n ] A = vec A n
{-# DISPLAY vec A n = vec[ n ] A #-}

matrix[_,_] : ℕ → ℕ → Set → Set
matrix[ m , n ] A = vec[ m ] (vec[ n ] A)

graph[_] : ℕ → Set
graph[ n ] = matrix[ n , n ] 𝔹

data idx : ℕ → Set where
  Z : ∀ {n} → idx (S n)
  S : ∀ {n} → idx n → idx (S n)

𝕚 : ∀ (m : ℕ) {n} {{_ : m <? n ≡ [<]}} → idx n
𝕚 Z {Z} {{()}}
𝕚 Z {S n} {{↯}} = Z
𝕚 (S m) {Z} {{()}}
𝕚 (S m) {S n} = S (𝕚 m {n})

infixl 40 _#[_]
_#[_] : ∀ {A : Set} {n : ℕ} → vec[ n ] A → idx n → A
(x ∷ xs) #[ Z ] = x
(x ∷ xs) #[ S ι ] = xs #[ ι ]

infixl 40 _#[_↦_]
_#[_↦_] : ∀ {A n} → vec[ n ] A → idx n → A → vec[ n ] A
(x ∷ xs) #[ Z ↦ x′ ] = x′ ∷ xs
(x ∷ xs) #[ S ι ↦ x′ ] = x ∷ (xs #[ ι ↦ x′ ])

_⋅_ : ∀ {m : ℕ} → vec[ m ] ℕ → vec[ m ] ℕ → ℕ
[] ⋅ [] = 0
(x ∷ xs) ⋅ (y ∷ ys) = x × y + xs ⋅ ys

_⧻_ : ∀ {A : Set} {m n : ℕ} → vec[ m ] A → vec[ n ] A → vec[ m + n ] A
[] ⧻ ys = ys
(x ∷ xs) ⧻ ys = x ∷ xs ⧻ ys

vlfold : ∀ {A B : Set} {n} → vec[ n ] A → B → (idx n → A → B → B) → B
vlfold [] i f = i
vlfold (x ∷ xs) i f = vlfold xs (f Z x i) (f ∘ S)

vrfold : ∀ {A B : Set} {n} → vec[ n ] A → B → (idx n → A → B → B) → B
vrfold [] i f = i
vrfold (x ∷ xs) i f = f Z x (vrfold xs i (f ∘ S))

build[_] : ∀ {A : Set} (n : ℕ) → (idx n → A) → vec[ n ] A
build[ Z ] f = []
build[ S n ] f = f Z ∷ build[ n ] (λ ι → f (S ι))

const[vec]<_> : ∀ {A : Set} (m : ℕ) → A → vec[ m ] A
const[vec]< Z > x = []
const[vec]< S m > x = x ∷ const[vec]< m > x 

map[vec] : ∀ {A B : Set} {m : ℕ} → (A → B) → vec[ m ] A → vec[ m ] B
map[vec] f [] = []
map[vec] f (x ∷ xs) = f x ∷ map[vec] f xs

return[vec] : ∀ {A : Set} → A → vec[ 1 ] A
return[vec] x = x ∷ []

_≫=[vec]_ : ∀ {A B : Set} {m n : ℕ} → vec[ m ] A → (A → vec[ n ] B) → vec[ m × n ] B
_≫=[vec]_ [] f = []
_≫=[vec]_ (x ∷ xs) f = f x ⧻ (xs ≫=[vec] f)

module monad-vec where
  return = return[vec]
  _>>=_ = _≫=[vec]_
  _>>_ : ∀ {A B m n} → vec[ m ] A → vec[ n ] B → vec[ m × n ] B
  xM >> yM = xM ≫=[vec] λ _ → yM

-- ======== --
-- POWERSET --
-- ======== --

record ℘ (A : Set) : Set where
  constructor 𝓅
  field φ : A → Set
open ℘ public

_∈_ : ∀ {A} → A → ℘ A → Set
x ∈ 𝓅 φ = φ x

{-# DISPLAY ℘.φ X x = x ∈ X #-}

_⊍_ : ∀ {A} → ℘ A → ℘ A → ℘ A
X ⊍ Y = 𝓅 λ x → x ∈ X ∨ x ∈ Y

_⩀_ : ∀ {A} → ℘ A → ℘ A → ℘ A
X ⩀ Y = 𝓅 λ x → x ∈ X ∧ x ∈ Y

-- ===== --
-- REALS --
-- ===== --

postulate
  ℝ : Set
  𝕣 : ℕ → ℝ
  _+ʳ_ : ℝ → ℝ → ℝ
  _-ʳ_ : ℝ → ℝ → ℝ
  _×ʳ_ : ℝ → ℝ → ℝ
  _/ʳ_ : ℝ → ℝ → ℝ
  _^ʳ_ : ℝ → ℝ → ℝ
  ⁻ʳ_ : ℝ → ℝ
  ㏑ : ℝ → ℝ
  𝑒^ : ℝ → ℝ

postulate
  lunit[+ʳ] : ∀ (x : ℝ) → 𝕣 0 +ʳ x ≡ x
  runit[+ʳ] : ∀ (x : ℝ) → x +ʳ 𝕣 0 ≡ x
  assoc[+ʳ] : ∀ (x y z : ℝ) → x +ʳ (y +ʳ z) ≡ (x +ʳ y) +ʳ z
  commu[+ʳ] : ∀ (x y : ℝ) → x +ʳ y ≡ y +ʳ x

  lunit[×ʳ] : ∀ (x : ℝ) → 𝕣 0 ×ʳ x ≡ x
  runit[×ʳ] : ∀ (x : ℝ) → x ×ʳ 𝕣 0 ≡ x
  lzero[×ʳ] : ∀ (x : ℝ) → 𝕣 0 ×ʳ x ≡ 𝕣 0
  rzero[×ʳ] : ∀ (x : ℝ) → x ×ʳ 𝕣 0 ≡ 𝕣 0
  assoc[×ʳ] : ∀ (x y z : ℝ) → x ×ʳ (y ×ʳ z) ≡ (x ×ʳ y) ×ʳ z
  commu[×ʳ] : ∀ (x y : ℝ) → x ×ʳ y ≡ y ×ʳ x
  ldist[×ʳ] : ∀ (x y z : ℝ) → x ×ʳ (y +ʳ z) ≡ x ×ʳ y +ʳ x ×ʳ z
  rdist[×ʳ] : ∀ (x y z : ℝ) → (x +ʳ y) ×ʳ z ≡ x ×ʳ z +ʳ y ×ʳ z

-- =========== --
-- PROBABILITY --
-- =========== --

record 𝒟 (A : Set) : Set where
  constructor 𝒹
  field ψ : A → ℝ
open 𝒟 public

Pr[_⩦_] : ∀ {A} → 𝒟 A → A → ℝ
Pr[ 𝒹 ψ ⩦ x ] = ψ x

{-# DISPLAY 𝒟.ψ X x = Pr[ X ⩦ x ] #-}

point : ∀ {A} → (A → A → ≡!) → A → 𝒟 A
point p x = 𝒹 λ y → CASE p x y OF λ where
  [≡] → 𝕣 1
  [≢] → 𝕣 0

-- ======== --
-- PATTERNS --
-- ======== --

pattern [_] a = a ∷ []
pattern [_,_] a b = a ∷ [ b ]
pattern [_,_,_] a b c = a ∷ [ b , c ]
pattern [_,_,_,_] a b c d = a ∷ [ b , c , d ]
pattern [_,_,_,_,_] a b c d e = a ∷ [ b , c , d , e ]
pattern [_,_,_,_,_,_] a b c d e f = a ∷ [ b , c , d , e , f ]
pattern [_,_,_,_,_,_,_] a b c d e f g = a ∷ [ b , c , d , e , f , g ]
pattern [_,_,_,_,_,_,_,_] a b c d e f g h = a ∷ [ b , c , d , e , f , g , h ]
pattern [_,_,_,_,_,_,_,_,_] a b c d e f g h i = a ∷ [ b , c , d , e , f , g , h , i ]
pattern [_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j = a ∷ [ b , c , d , e , f , g , h , i , j ]

-- ===== --
-- WORDS --
-- ===== --

postulate ℕ64 : Set
{-# BUILTIN WORD64 ℕ64 #-}

module _ where
  private
    primitive
      primWord64ToNat   : ℕ64 → ℕ
      primWord64FromNat : ℕ → ℕ64
  𝕟-fr-𝕟64 = primWord64ToNat
  𝕟64-fr-𝕟 = primWord64FromNat

-- ====== --
-- FLOATS --
-- ====== --

postulate 𝔽 : Set
{-# BUILTIN FLOAT 𝔽 #-}

module _ where
  private
    primitive
      primFloatEquality : 𝔽 → 𝔽 → 𝔹
      primFloatLess : 𝔽 → 𝔽 → 𝔹
      primFloatNumericalEquality : 𝔽 → 𝔽 → 𝔹
      primFloatNumericalLess : 𝔽 → 𝔽 → 𝔹
      primNatToFloat : ℕ → 𝔽
      primFloatPlus : 𝔽 → 𝔽 → 𝔽
      primFloatMinus : 𝔽 → 𝔽 → 𝔽
      primFloatTimes : 𝔽 → 𝔽 → 𝔽
      primFloatNegate : 𝔽 → 𝔽
      primFloatDiv : 𝔽 → 𝔽 → 𝔽
      primFloatSqrt : 𝔽 → 𝔽
      primRound : 𝔽 → ℤ
      primFloor : 𝔽 → ℤ
      primCeiling : 𝔽 → ℤ
      primExp : 𝔽 → 𝔽
      primLog : 𝔽 → 𝔽
      primSin : 𝔽 → 𝔽
      primCos : 𝔽 → 𝔽
      primTan : 𝔽 → 𝔽
      primASin : 𝔽 → 𝔽
      primACos : 𝔽 → 𝔽
      primATan : 𝔽 → 𝔽
      primATan2 : 𝔽 → 𝔽 → 𝔽
  infix 24 _≡?ᶠ_
  infix 24 _<?ᶠ_
  infix 24 _≈?ᶠ_
  infix 24 _≺?ᶠ_
  infixl 25 _+ᶠ_
  infixl 25 _-ᶠ_
  infixl 26 _×ᶠ_
  infixl 26 _/ᶠ_
  infixr 30 ⁻ᶠ_
  _≡?ᶠ_ = primFloatEquality
  _<?ᶠ_ = primFloatLess
  _≈?ᶠ_ = primFloatNumericalEquality
  _≺?ᶠ_ = primFloatNumericalLess
  𝕗 = primNatToFloat
  _+ᶠ_ = primFloatPlus
  _-ᶠ_ = primFloatMinus
  _×ᶠ_ = primFloatTimes
  ⁻ᶠ_ =  primFloatNegate
  _/ᶠ_ = primFloatDiv
  √ᶠ = primFloatSqrt
  ‖_‖ᶠ = primRound
  ⌊_⌋ᶠ = primFloor
  ⌈_⌉ʳ = primCeiling
  e^ᶠ = primExp
  ㏑ᶠ = primLog
  sinᶠ = primSin
  cosᶠ = primCos
  tanᶠ = primTan
  asinᶠ = primASin
  acosᶠ = primACos
  atanᶠ = primATan
  atan2ᶠ = primATan2

_ : √ᶠ 4.0 ≡ 2.0
_ = ↯

module UnsafeFloatLaws where
  postulate
    lunit[+ᶠ] : ∀ (x : 𝔽) → 0.0 +ᶠ x ≡ x
    runit[+ᶠ] : ∀ (x : 𝔽) → x +ᶠ 0.0 ≡ x
    assoc[+ᶠ] : ∀ (x y z : 𝔽) → x +ᶠ (y +ᶠ z) ≡ (x +ᶠ y) +ᶠ z
    commu[+ᶠ] : ∀ (x y : 𝔽) → x +ᶠ y ≡ y +ᶠ x
  
    lunit[×ᶠ] : ∀ (x : 𝔽) → 1.0 ×ᶠ x ≡ x
    runit[×ᶠ] : ∀ (x : 𝔽) → x ×ᶠ 1.0 ≡ x
    lzero[×ᶠ] : ∀ (x : 𝔽) → 0.0 ×ᶠ x ≡ 0.0
    rzero[×ᶠ] : ∀ (x : 𝔽) → x ×ᶠ 0.0 ≡ 0.0
    assoc[×ᶠ] : ∀ (x y z : 𝔽) → x ×ᶠ (y ×ᶠ z) ≡ (x ×ᶠ y) ×ᶠ z
    commu[×ᶠ] : ∀ (x y : 𝔽) → x ×ᶠ y ≡ y ×ᶠ x
    ldist[×ᶠ] : ∀ (x y z : 𝔽) → x ×ᶠ (y +ᶠ z) ≡ x ×ᶠ y +ᶠ x ×ᶠ z
    rdist[×ᶠ] : ∀ (x y z : 𝔽) → (x +ᶠ y) ×ᶠ z ≡ x ×ᶠ z +ᶠ y ×ᶠ z

-- ===== --
-- CHARS --
-- ===== --

postulate ℂ : Set
{-# BUILTIN CHAR ℂ #-}

primitive
  primIsLower : ℂ → 𝔹
  primIsDigit : ℂ → 𝔹
  primIsAlpha : ℂ → 𝔹
  primIsSpace : ℂ → 𝔹
  primIsAscii : ℂ → 𝔹
  primIsLatin1 : ℂ → 𝔹
  primIsPrint : ℂ → 𝔹
  primIsHexDigit : ℂ → 𝔹
  primToUpper primToLower : ℂ → ℂ
  primCharToNat : ℂ → ℕ
  primNatToChar : ℕ → ℂ
  primCharEquality : ℂ → ℂ → 𝔹

-- ======= --
-- STRINGS --
-- ======= --

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}

postulate 𝕊 : Set
{-# BUILTIN STRING 𝕊 #-}

primitive
  primStringToList   : 𝕊 → list ℂ
  primStringFromList : list ℂ → 𝕊
  primStringAppend   : 𝕊 → 𝕊 → 𝕊
  primStringEquality : 𝕊 → 𝕊 → 𝔹
  primShowChar       : ℂ → 𝕊
  primShowString     : 𝕊 → 𝕊

postulate
  show-𝕟 : ℕ → 𝕊
{-# COMPILE GHC show-𝕟 = Text.pack . show #-}

show-𝕟64 : ℕ64 → 𝕊
show-𝕟64 = show-𝕟 ∘ 𝕟-fr-𝕟64

-- == --
-- IO --
-- == --

postulate io : Set → Set
{-# BUILTIN IO io #-}
{-# COMPILE GHC io = type IO #-}

postulate
  _≫=[io]_ : ∀ {A B} → io A → (A → io B) → io B
  return[io] : ∀ {A} → A → io A
  print : 𝕊 → io 𝟙

{-# COMPILE GHC _≫=[io]_ = \ _ _ -> (>>=) #-}
{-# COMPILE GHC return[io] = \ _ -> return #-}
{-# COMPILE GHC print = Text.putStrLn #-}

module monad-io where
  return = return[io]
  _>>=_ = _≫=[io]_
  _>>_ : ∀ {A B} → io A → io B → io B
  xM >> yM = xM ≫=[io] λ _ → yM

----------------
-- RANDOMNESS --
----------------

postulate
  rand𝕟64 : io ℕ64
{-# FOREIGN GHC import qualified System.Random as Random #-}
{-# COMPILE GHC rand𝕟64 = Random.randomIO #-}

------------------
-- EXAMPLE MAIN --
------------------

basics-main : io 𝟙
basics-main = let open monad-io in do
  print "hello world"
  print "hi"
  n ← rand𝕟64
  print $ show-𝕟64 n
