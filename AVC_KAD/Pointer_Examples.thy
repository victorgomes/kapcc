theory Pointer_Examples
  imports VC_KAD_Examples "$ISABELLE_HOME/src/HOL/Hoare/Heap"
begin

type_synonym 'a state = "string  \<Rightarrow> ('a ref + ('a \<Rightarrow> 'a ref))"

lemma list_reversal:
  "PRE (\<lambda>s :: 'a state. List (projr (s ''h'')) (projl (s ''p'')) Ps 
        \<and> List (projr (s ''h'')) (projl (s ''q'')) Qs 
        \<and> set Ps \<inter> set Qs = {})
    (WHILE (\<lambda>s. projl (s ''p'') \<noteq> Null) 
     INV (\<lambda>s. \<exists>ps qs. List (projr (s ''h'')) (projl (s ''p'')) ps 
              \<and> List (projr (s ''h'')) (projl (s ''q'')) qs 
              \<and> set ps \<inter> set qs = {} \<and> rev ps @ qs = rev Ps @ Qs)
     DO
      (''r'' ::= (\<lambda>s. s ''p''));
      (''p'' ::= (\<lambda>s. Inl (projr (s ''h'') (addr (projl (s ''p''))))) );
      (''h'' ::= (\<lambda>s. Inr ((projr (s ''h''))(addr (projl (s ''r'')) := projl (s ''q''))) ));
      (''q'' ::= (\<lambda>s. s ''r''))
     OD)
  POST (\<lambda>s. List (projr (s ''h'')) (projl (s ''q'')) (rev Ps @ Qs))"
  apply hoare
  apply auto
  apply(fastforce intro: notin_List_update[THEN iffD2])
done


end