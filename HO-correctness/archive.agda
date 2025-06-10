
identityPrecond-is-identity-f : {Γ : Env Pr}
    → (isRd : Is-ℝᵈ (Etup Pr Γ))
    → (x : Rep (Etup Pr Γ))
    → FL-f-val isRd (identityPrecond Γ isRd) x 
      ≡ Etup-to-val x
identityPrecond-is-identity-f {Γ} isRd x = 
    let lemma = ValIdProjections-is-Id Γ isRd Γ (LensId (Etup Pr Γ) isRd) x 
    in cong Etup-to-val (sym (trans (sym lemma) (cong (HL-to-Etup {Γ = Γ}) 
        (trans₂ (HL-map-equiv (λ a v → refl))
                (sym (HL-map-chain (λ τ → project) (λ τ f → f x) _)) 
                (sym (HL-map-chain (IdProjectionToPrecond isRd) (λ _ y → y .fst .fst x) (ValIdProjections Γ isRd Γ (LensId (Etup Pr Γ) isRd))))))))
    where   ValIdProjections-is-Id : (Γ : Env Pr) → (q : Is-ℝᵈ (Etup Pr Γ)) 
                → (G : Env Pr) 
                → (L : Lens (Etup Pr Γ) (Etup Pr G) q)
                → let lenses = ValIdProjections Γ q G L
                      projections = HL-map (λ τ l → project l) lenses
                in (xs : Rep (Etup Pr Γ))
                → HL-to-Etup (HL-map (λ τ f → f xs) projections) ≡ project L xs
            ValIdProjections-is-Id Γ q [] L xs = refl
            ValIdProjections-is-Id Γ q (τ ∷ G) L xs = 
                let ih = ValIdProjections-is-Id Γ q G (lensTakeSnd L) xs
                in sub-× refl (sym (Etup-≡-HL G)) (sym (cong₂ _×_ refl (Etup-≡-HL G))) (sym (lensTakeFst-lemma L xs)) 
                        (trans ih (sym (lensTakeSnd-lemma L xs)))

identityPrecond-is-identity-f' : {Γ : Env Pr}
    → (isRd : Is-ℝᵈ (Etup Pr Γ))
    → (x : Rep (D1τ (Etup Pr Γ)))
    → FL-f'-val isRd (identityPrecond Γ isRd) x 
      ≡ Etup-to-val (Etup-D1τ-distr₁ Γ x)
identityPrecond-is-identity-f' {Γ} isRd x = 
   cong Etup-to-val 
      (trans (sub-chain (lemma-D1Γ≡ isRd) (sym (Etup-≡-HL (map D1τ Γ)))) 
      (sub-move (trans (lemma-D1Γ≡ isRd) (sym (Etup-≡-HL (map D1τ Γ)))) (cong Rep (Etup-D1τ-distr≡ Γ)) 
      (trans (HL-map-chain (IdProjectionToPrecond isRd) (λ a y → y .fst .snd x .fst) (ValIdProjections Γ isRd Γ (LensId (Etup Pr Γ) isRd))) 
      (ValIdProjections-is-Id Γ isRd Γ (LensId (Etup Pr Γ) isRd) x))))
    where 
          lemma1 : {τ : Typ Pr} { Γ : Env Pr }
              → (q : Is-ℝᵈ (Etup Pr Γ)) 
              → (G` : Env Pr) 
              → let G = τ ∷ G`
              in (L : Lens (Etup Pr Γ) (Etup Pr G) q)
              → (xs : Rep (D1τ (Etup Pr Γ)))
                →  (project (lens-primal L) xs) .fst
                 ≡ (IdProjectionToPrecond q τ (lensTakeFst L) .fst .snd xs .fst)
          lemma1 {τ} {Γ} q G L xs = trans (cong fst (lens-primal-lemma {q2 = Lens-preserves-ℝᵈ L} L xs))
                                    (cong₂ to-primal (Is-ℝᵈ-irrel (Lens-preserves-ℝᵈ L .fst) (Lens-preserves-ℝᵈ (lensTakeFst L))) 
                                                       (lensTakeFst-lemma L (un-primal q xs)))

          lemma2 : { σ τ1 τ2 : Typ Pr }
              → (q : Is-ℝᵈ σ) 
              → (L : Lens σ (τ1 :* τ2) q)
              → (xs : Rep (D1τ σ))
              → (project (lens-primal (lensTakeSnd L)) xs)
              ≡ (project (lensTakeSnd (lens-primal L)) xs)
          lemma2 q (LensFst σ1 σ2 .(_ :* _) .q L) xs = lemma2 (fst q) L (fst xs)
          lemma2 q (LensSnd σ1 σ2 .(_ :* _) .q L) xs = lemma2 (snd q) L (snd xs)
          lemma2 q (LensId .(_ :* _) .q) xs = refl

          lemma3 : ∀ {G} → Rep (D1τ (Etup Pr G)) ≡ HL G (Rep ∘ D1τ)
          lemma3 {[]} = refl
          lemma3 {x ∷ G} = cong₂ _×_ refl lemma3

          ValIdProjections-is-Id : 
             (Γ : Env Pr) → (q : Is-ℝᵈ (Etup Pr Γ)) 
              → (G : Env Pr) 
              → (L : Lens (Etup Pr Γ) (Etup Pr G) q)
              → (xs : Rep (D1τ (Etup Pr Γ)))
              → let lenses = ValIdProjections Γ q G L
                    projections = HL-map (λ a l → IdProjectionToPrecond q a l .fst .snd xs .fst) lenses
                    w = (trans (cong Rep (Etup-D1τ-distr≡ G)) (sym (trans (lemma-D1Γ≡ (Lens-preserves-ℝᵈ L)) (sym (Etup-≡-HL (map D1τ G))))))
              in projections ≡ sub w (project (lens-primal L) xs)
          ValIdProjections-is-Id Γ q [] L xs = refl
          ValIdProjections-is-Id Γ q (τ ∷ G) L xs = 
              let ih = ValIdProjections-is-Id Γ q G (lensTakeSnd L) xs
              in sub-× refl refl refl 
                       (sym (trans (sub-fst ((trans (cong Rep (cong₂ _:*_ refl (Etup-D1τ-distr≡ G))) (sym (trans (lemma-D1Γ≡ (Lens-preserves-ℝᵈ L)) (sym (Etup-≡-HL (map D1τ (τ ∷ G)))))))) 
                                            lemma3 
                                            (project (lens-primal L) xs)) 
                                    (lemma1 q G L xs))) 
                      (sym (trans (sub-snd ((trans (cong Rep (cong₂ _:*_ refl (Etup-D1τ-distr≡ G))) (sym (trans (lemma-D1Γ≡ (Lens-preserves-ℝᵈ L)) (sym (Etup-≡-HL (map D1τ (τ ∷ G)))))))) 
                                          refl lemma3 (project (lens-primal L) xs)) 
                                  (trans (cong (sub lemma3) (lensTakeSnd-lemma (lens-primal L) xs)) 
                                  (sym (trans ih (sub-cong _ lemma3 (lemma2 q L xs)))))))


FL-f'-with-identity : {Γ : Env Pr} {τ : Typ Pr}
    → (isRd : Is-ℝᵈ (Etup Pr Γ))
    → (t : Term Pr Γ τ)
    → (x : Rep (D1τ (Etup Pr Γ)))
    → (ctg : LinRep (D2τ' τ)) 
    → (FL-f' isRd (identityPrecond Γ isRd) t x .snd ctg)
      ≡ (LR-chad isRd t (zero-LEtup Γ) x .snd ctg)
FL-f'-with-identity {Γ} {τ} isRd t x ctg = 
    sym {!   !}


chad-in-LR : {Γ : Env Pr} {τ : Typ Pr}
    → let σ = Etup Pr Γ
          LΓ = map D2τ' Γ
      in (isRd : Is-ℝᵈ σ)
    → (t : Term Pr Γ τ)
    → LR σ isRd τ (interp t ∘ Etup-to-val) (LR-chad isRd t (zero-LEtup Γ))
chad-in-LR {Γ} {τ} isRd t =
    ext
    where input = identityPrecond Γ isRd
          funlemma = fundamental-lemma Γ τ isRd input t
          equiv = (λ x → cong (interp t) (identityPrecond-is-identity-f isRd x)) 
                  , (λ x → cong ( λ q → interp (chad t) q .fst) (identityPrecond-is-identity-f' isRd x) 
                  , λ ctg → FL-f'-with-identity isRd t x ctg)
          ext = LR-extensionality isRd (FL-f isRd input t) (FL-f' isRd input t) (interp t ∘ Etup-to-val) (LR-chad isRd t (zero-LEtup Γ)) equiv funlemma