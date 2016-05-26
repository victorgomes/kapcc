theory VC_KAD_wf_Examples
  imports VC_KAD_wf
begin

lemma [simp]: "wp \<lceil>P\<rceil> \<lceil>Q\<rceil> = \<lceil>-P \<squnion> Q\<rceil>"
  by (simp add: rel_antidomain_kleene_algebra.fbox_def)

lemma [intro!]:  "P \<le> Q \<Longrightarrow> \<lceil>P\<rceil> \<subseteq> \<lceil>Q\<rceil>"
  by (force simp: p2r_def)

lemma [intro!]: "P = Q \<Longrightarrow> \<lceil>P\<rceil> = \<lceil>Q\<rceil>"
  by simp

lemma euclid:
  "rel_nabla (
    \<lceil>\<lambda>s::nat store. 0 < s ''y''\<rceil> ; 
      ((''z'' ::= (\<lambda>s. s ''y'')) ; 
      (''y'' ::= (\<lambda>s. s ''x'' mod s ''y'')) ;
      (''x'' ::= (\<lambda>s. s ''z'')))) 
    = {}
    \<Longrightarrow>
  PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y)
   (WHILE (\<lambda>s. s ''y'' \<noteq> 0) INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    DO
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    OD)
   POST (\<lambda>s. s ''x'' = gcd x y)"
  apply (subst rel_fdivka.fbox_arden_whilei[symmetric])
  apply auto
  apply (rule ext)
  using gcd_red_nat apply auto[1]
  using gr0I apply force
done

end