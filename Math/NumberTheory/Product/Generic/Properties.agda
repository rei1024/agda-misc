{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Product.Generic.Properties where

-- agda-stdlib
open import Algebra

-- agda-misc
open import Math.NumberTheory.Summation.Generic.Properties

-- TODO add renamaings
module CommutativeMonoidProductProperties {c e} (CM : CommutativeMonoid c e) =
  CommutativeMonoidSummationProperties CM
  renaming
  ( Σ<-cong to Π<-cong
  ; Σ<-congˡ to Π<-congˡ
  ; Σ<-congʳ to Π<-congʳ
  ; Σ≤-cong to Π≤-cong
  ; Σ≤-congˡ to Π≤-congˡ
  ; Σ≤-congʳ to Π≤-congʳ
  ; Σ<-0 to Π<-1
  ; Σ≤-0 to Π≤-1
  ; Σ<[f,1]≈f[0] to Π<[f,1]≈f[0]
  ; Σ≤[f,0]≈f[0] to Π≤[f,0]≈f[0]
  ; Σ<-+ to Π<-+
  ; Σ<-push-suc to Π<-push-suc
  ; Σ<-const to Π<-const
  ; Σ≤-const to Π≤-const
  ; Σ<-distrib-+ to Π<-distrib-*
  ; Σ≤-distrib-+ to Π≤-distrib-*
  ; Σ<-comm to Π<-comm
  ; Σ≤-comm to Π≤-comm
  )
  using ()
