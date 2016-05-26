section {* Every Kleene algebra with domain is a Kleene algebra with tests *}

theory KAD_is_KAT

imports "$AFP/KAD/Antidomain_Semiring" 
        "$AFP/KAT_and_DRA/SingleSorted/KAT"
        "AVC_KAD/VC_KAD"
        "AVC_KAT/VC_KAT"
begin

context antidomain_kleene_algebra
begin

sublocale kat "op +" "op \<cdot>" "1" "0" "op \<le>" "op <" star antidomain_op
  apply standard
  apply simp
  using local.a_d_mult_closure local.am_d_def apply auto[1]
  using local.dpdz.dom_weakly_local apply auto[1]
  using local.a_d_add_closure local.a_de_morgan by presburger

lemma H_kat_to_kad: "H p x q \<longleftrightarrow> d p \<le> |x] (d q)"
  using local.H_def local.addual.ars_r_def local.fbox_demodalisation3 by auto

end
 
lemma H_eq: "P \<le> Id \<Longrightarrow> Q \<le> Id \<Longrightarrow> rel_kat.H P X Q = rel_antidomain_kleene_algebra.H P X Q"
  apply (simp add: rel_kat.H_def rel_antidomain_kleene_algebra.H_def)
  apply (subgoal_tac "rel_antidomain_kleene_algebra.t P = Id \<inter> P")
  apply (subgoal_tac "rel_antidomain_kleene_algebra.t Q = Id \<inter> Q")
  apply simp
  apply (auto simp: rel_ad_def)
done

(* hiding notation for VC_KAD *)
no_notation VC_KAD.spec_sugar ("PRE _ _ POST _" [64,64,64] 63)
and VC_KAD.cond_sugar ("IF _ THEN _ ELSE _ FI" [64,64,64] 63)
and VC_KAD.gets ("_ ::= _" [70, 65] 61)

lemma maximum: 
  "PRE (\<lambda>s:: nat store. True)
   (IF (\<lambda>s. s ''x'' \<ge> s ''y'') 
    THEN (''z'' ::= (\<lambda>s. s ''x''))
    ELSE (''z'' ::= (\<lambda>s. s ''y''))
    FI)
   POST (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))"
  by (simp only: sH_cond_iff H_assign_iff, auto)

lemma H_from_kat: "PRE p x POST q = (\<lceil>p\<rceil> \<le> (rel_antidomain_kleene_algebra.fbox x) \<lceil>q\<rceil>)"
  apply (subst H_eq)
  apply (clarsimp simp add: p2r_def)
  apply (clarsimp simp add: p2r_def)
  apply (subst rel_antidomain_kleene_algebra.H_kat_to_kad)
  apply (subgoal_tac "rel_antidomain_kleene_algebra.ads_d \<lceil>p\<rceil> = \<lceil>p\<rceil>")
  apply (subgoal_tac "rel_antidomain_kleene_algebra.ads_d \<lceil>q\<rceil> = \<lceil>q\<rceil>")
  apply simp
  apply (auto simp: rel_antidomain_kleene_algebra.ads_d_def rel_ad_def p2r_def)
done

lemma cond_iff: "rel_kat.ifthenelse \<lceil>P\<rceil> X Y = rel_antidomain_kleene_algebra.cond \<lceil>P\<rceil> X Y"
  by (auto simp: rel_kat.ifthenelse_def rel_antidomain_kleene_algebra.cond_def)

lemma gets_iff: "v ::= e = VC_KAD.gets v e"
  by (auto simp: VC_KAT.gets_def VC_KAD.gets_def)


lemma maximum2: 
  "PRE (\<lambda>s:: nat store. True)
   (IF (\<lambda>s. s ''x'' \<ge> s ''y'') 
    THEN (''z'' ::= (\<lambda>s. s ''x''))
    ELSE (''z'' ::= (\<lambda>s. s ''y''))
    FI)
   POST (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))"
   apply (subst H_from_kat)
   apply (subst cond_iff)
   apply (subst gets_iff)
   apply (subst gets_iff)
   apply auto
done

end


