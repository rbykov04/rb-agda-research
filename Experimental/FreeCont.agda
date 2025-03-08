module FreeCont where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive


-- Определим базовый уровень типов
--
private
  variable
    a b c d e : Level

-- Определим конструктор для расширенного типа
data Ext {ℓ₁ ℓ₂ : Level} (S : Set ℓ₁) (P : S → Set → Set → Set) (M : Set → Set) (A : Set) : Set where
  ext : ∀ s → ((X : Set) → P s A X → M X) → Ext S P M A

-- Определим класс контейнеров
record HContainer {ℓ₁ ℓ₂ : Level} (H : (Set → Set) → Set → Set) : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    shape : Set ℓ₁
    position : shape → Set → Set → Set
    to : ∀ {M A} → Ext shape position M A → H M A
    from : ∀ {M A} → H M A → Ext shape position M A
    to-from : ∀ {M A} {fx : H M A} → to (from fx) ≡ fx
    from-to : ∀ {M A} {e : Ext shape position M A} → from (to e) ≡ e

-- Определим свободную монаду
data Free {ℓ₁ ℓ₂ : Level} (HC : HContainer {ℓ₁} {ℓ₂}) (A : Set) : Set where
  pure : A → Free HC A
  impure : Ext (HContainer.shape HC) (HContainer.position HC) (Free HC) A → Free HC A
