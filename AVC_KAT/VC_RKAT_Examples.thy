section {* Example Refinement Proofs with RKAT *}

theory VC_RKAT_Examples
  imports VC_RKAT

begin

text {* Currently  there is only one example. *}

lemma var_swap_ref1: 
  "rel_R \<lceil>\<lambda>s. s ''x'' = a \<and> s ''y'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil>
   \<supseteq> (''z'' ::= (\<lambda>s. s ''x'')); rel_R \<lceil>\<lambda>s. s ''z'' = a \<and> s ''y'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil>"
  by (rule R_assignl, auto) 

lemma var_swap_ref2: 
  "rel_R \<lceil>\<lambda>s. s ''z'' = a \<and> s ''y'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil> 
   \<supseteq> (''x'' ::= (\<lambda>s. s ''y'')); rel_R \<lceil>\<lambda>s. s ''z'' = a \<and> s ''x'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil>"
  by (rule R_assignl, auto)

lemma var_swap_ref3:  
  "rel_R \<lceil>\<lambda>s. s ''z'' = a \<and> s ''x'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil>
   \<supseteq> (''y'' ::= (\<lambda>s. s ''z'')); rel_R \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil>" 
  by (rule R_assignl, auto)

lemma var_swap_ref_var: 
  "rel_R \<lceil>\<lambda>s. s ''x'' = a \<and> s ''y'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil>
   \<supseteq> (''z'' ::= (\<lambda>s. s ''x'')); (''x'' ::= (\<lambda>s. s ''y'')); (''y'' ::= (\<lambda>s. s ''z''))"
  using var_swap_ref1 var_swap_ref2 var_swap_ref3 rel_rkat.R_skip  by fastforce

end


