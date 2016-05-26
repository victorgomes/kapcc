section{* Example Verifications with KAD *}

theory VC_KAD_Examples
imports VC_KAD GCD Binomial "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach"

begin

lemma [simp]: "p2r P \<union> p2r Q = p2r (P \<squnion> Q)"
  by (simp add: p2r_disj_hom)

lemma [simp]: "p2r P; p2r Q = p2r (P \<sqinter> Q)"
  by (simp add: p2r_conj_hom_var)

lemma [intro!]:  "P \<le> Q \<Longrightarrow> \<lceil>P\<rceil> \<subseteq> \<lceil>Q\<rceil>"
  by (auto simp: p2r_def)

lemma [simp]: "rdom \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  by (simp add: d_p2r)

lemma euclid:
  "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y)
   (WHILE (\<lambda>s. s ''y'' \<noteq> 0) INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    DO
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    OD)
   POST (\<lambda>s. s ''x'' = gcd x y)"
  by (rule rel_antidomain_kleene_algebra.fbox_whilei) (auto simp: gcd_non_0_nat)

lemma euclid_diff: 
   "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y \<and> x > 0 \<and> y > 0)
    (WHILE (\<lambda>s. s ''x''\<noteq> s ''y'') INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
     DO
        (IF (\<lambda>s. s ''x'' >  s ''y'')
         THEN (''x'' ::= (\<lambda>s. s ''x'' - s ''y''))
         ELSE (''y'' ::= (\<lambda>s. s ''y'' - s ''x''))
         FI)
    OD)
    POST (\<lambda>s. s ''x'' = gcd x y)"
  apply (rule rel_antidomain_kleene_algebra.fbox_whilei, simp_all)
  apply (simp_all add: p2r_def rel_ad_def) 
  apply auto[2]
  by (safe, metis gcd_commute_nat gcd_diff1_nat le_cases nat_less_le)

lemma varible_swap:
  "PRE (\<lambda>s. s ''x'' = a \<and> s ''y'' = b)   
    (''z'' ::= (\<lambda>s. s ''x''));
    (''x'' ::= (\<lambda>s. s ''y''));
    (''y'' ::= (\<lambda>s. s ''z''))
   POST (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)"
  by (simp, clarsimp simp: p2r_def)

lemma maximum: 
  "PRE (\<lambda>s:: nat store. True) 
   (IF (\<lambda>s. s ''x'' \<ge> s ''y'') 
    THEN (''z'' ::= (\<lambda>s. s ''x''))
    ELSE (''z'' ::= (\<lambda>s. s ''y''))
    FI)
   POST (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))"
  by (simp, simp add: p2r_def rel_ad_def, fastforce)

lemma integer_division: 
  "PRE (\<lambda>s::nat store. x \<ge> 0)
    (''q'' ::= (\<lambda>s. 0)); 
    (''r'' ::= (\<lambda>s. x));
    (WHILE (\<lambda>s. y \<le> s ''r'') INV (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0)
     DO
      (''q'' ::= (\<lambda>s. s ''q'' + 1));
      (''r'' ::= (\<lambda>s. s ''r'' - y))
      OD)
   POST (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0 \<and> s ''r'' < y)"
  by (rule rel_antidomain_kleene_algebra.fbox_whilei_break, simp_all, auto simp: p2r_def)

lemma factorial:
  "PRE (\<lambda>s::nat store. True)
   (''x'' ::= (\<lambda>s. 0));
   (''y'' ::= (\<lambda>s. 1));
   (WHILE (\<lambda>s. s ''x'' \<noteq> x0) INV (\<lambda>s. s ''y'' = fact (s ''x''))
   DO
     (''x'' ::= (\<lambda>s. s ''x'' + 1));
     (''y'' ::= (\<lambda>s. s ''y'' \<cdot> s ''x''))
   OD)
   POST (\<lambda>s. s ''y'' = fact x0)"
  by (rule rel_antidomain_kleene_algebra.fbox_whilei_break, simp_all, auto simp: p2r_def)
 
lemma my_power:
  "PRE (\<lambda>s::nat store. True)
   (''i'' ::= (\<lambda>s. 0));
   (''y'' ::= (\<lambda>s. 1));
   (WHILE (\<lambda>s. s ''i'' < n) INV (\<lambda>s. s ''y'' = x ^ (s ''i'') \<and> s ''i'' \<le> n)
     DO
       (''y'' ::= (\<lambda>s. (s ''y'') * x));
       (''i'' ::= (\<lambda>s. s ''i'' + 1))
     OD)
   POST (\<lambda>s. s ''y'' = x ^ n)"
  by (rule rel_antidomain_kleene_algebra.fbox_whilei_break, simp_all, auto simp add: p2r_def)

lemma imp_reverse:
  "PRE (\<lambda>s:: 'a list store. s ''x'' = X)
   (''y'' ::= (\<lambda>s. []));
   (WHILE (\<lambda>s. s ''x'' \<noteq> []) INV (\<lambda>s. rev (s ''x'') @ s ''y'' = rev X)
    DO 
     (''y'' ::= (\<lambda>s. hd (s ''x'') # s ''y'')); 
     (''x'' ::= (\<lambda>s. tl (s ''x'')))
    OD) 
   POST (\<lambda>s. s ''y''= rev X )"
  apply (rule rel_antidomain_kleene_algebra.fbox_whilei_break, simp_all, simp_all add: p2r_def)
  apply auto[1]
  by (safe, metis append.simps append_assoc hd_Cons_tl rev.simps(2))


(* using a tactic *)

named_theorems ht

declare rel_antidomain_kleene_algebra.fbox_whilei [ht]
  rel_antidomain_kleene_algebra.fbox_seq_var [ht]
  subset_refl[ht]

method hoare = (rule ht; hoare?)

lemma euclid2:
  "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y)
   (WHILE (\<lambda>s. s ''y'' \<noteq> 0) INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    DO
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    OD)
   POST (\<lambda>s. s ''x'' = gcd x y)"
apply hoare
using gcd_red_nat by auto

lemma euclid_diff2: 
   "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y \<and> x > 0 \<and> y > 0)
    (WHILE (\<lambda>s. s ''x''\<noteq> s ''y'') INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
     DO
        (IF (\<lambda>s. s ''x'' >  s ''y'')
         THEN (''x'' ::= (\<lambda>s. s ''x'' - s ''y''))
         ELSE (''y'' ::= (\<lambda>s. s ''y'' - s ''x''))
         FI)
    OD)
    POST (\<lambda>s. s ''x'' = gcd x y)"
  apply hoare
  apply auto
  apply (metis gcd_commute_nat gcd_diff1_nat le_cases nat_less_le)+
done

lemma varible_swap2:
  "PRE (\<lambda>s. s ''x'' = a \<and> s ''y'' = b)   
    (''z'' ::= (\<lambda>s. s ''x''));
    (''x'' ::= (\<lambda>s. s ''y''));
    (''y'' ::= (\<lambda>s. s ''z''))
   POST (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)"
  by clarsimp

lemma maximum2: 
  "PRE (\<lambda>s:: nat store. True) 
   (IF (\<lambda>s. s ''x'' \<ge> s ''y'') 
    THEN (''z'' ::= (\<lambda>s. s ''x''))
    ELSE (''z'' ::= (\<lambda>s. s ''y''))
    FI)
   POST (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))"
   by auto

lemma integer_division2: 
  "PRE (\<lambda>s::nat store. x \<ge> 0)
    (''q'' ::= (\<lambda>s. 0)); 
    (''r'' ::= (\<lambda>s. x));
    (WHILE (\<lambda>s. y \<le> s ''r'') INV (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0)
     DO
      (''q'' ::= (\<lambda>s. s ''q'' + 1));
      (''r'' ::= (\<lambda>s. s ''r'' - y))
      OD)
   POST (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0 \<and> s ''r'' < y)"
   by hoare auto

lemma my_power2:
  "PRE (\<lambda>s::nat store. True)
   (''i'' ::= (\<lambda>s. 0));
   (''y'' ::= (\<lambda>s. 1));
   (WHILE (\<lambda>s. s ''i'' < n) INV (\<lambda>s. s ''y'' = x ^ (s ''i'') \<and> s ''i'' \<le> n)
     DO
       (''y'' ::= (\<lambda>s. (s ''y'') * x));
       (''i'' ::= (\<lambda>s. s ''i'' + 1))
     OD)
   POST (\<lambda>s. s ''y'' = x ^ n)"
  by hoare auto

lemma imp_reverse2:
  "PRE (\<lambda>s:: 'a list store. s ''x'' = X)
   (''y'' ::= (\<lambda>s. []));
   (WHILE (\<lambda>s. s ''x'' \<noteq> []) INV (\<lambda>s. rev (s ''x'') @ s ''y'' = rev X)
    DO 
     (''y'' ::= (\<lambda>s. hd (s ''x'') # s ''y'')); 
     (''x'' ::= (\<lambda>s. tl (s ''x'')))
    OD) 
   POST (\<lambda>s. s ''y''= rev X )"
  apply hoare
  apply auto
  apply (metis append.simps append_assoc hd_Cons_tl rev.simps(2))
done

end