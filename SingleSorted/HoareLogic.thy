theory HoareLogic
  imports KAT
begin
context KAT
begin

notation comp_operator ("!_" [101] 100)

definition hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>") where
  "\<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<equiv> p\<cdot>c = p\<cdot>c\<cdot>q \<and> test p \<and> test q"

declare hoare_triple_def [simp]
declare test_def [simp]

lemma hoare_triple_def_var: "\<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> = (p\<cdot>c \<le> c\<cdot>q \<and> test p \<and> test q)"
  by (metis hoare_triple_def kat_eq1 kat_eq2)

lemma skip_rule: "test p \<Longrightarrow> \<lbrace>p\<rbrace>1\<lbrace>p\<rbrace>"
  by (simp, metis test_mult_idem)

lemma sequence_rule: "\<lbrace>p\<rbrace>c\<lbrace>q'\<rbrace> \<and> \<lbrace>q'\<rbrace>c'\<lbrace>q\<rbrace> \<Longrightarrow> \<lbrace>p\<rbrace>c\<cdot>c'\<lbrace>q\<rbrace>"
  by (simp, metis mult_assoc)

lemma conditional_rule: "\<lbrakk>test p; test b; \<lbrace>p\<cdot>b\<rbrace>c\<lbrace>q\<rbrace>; \<lbrace>p\<cdot>!b\<rbrace>c'\<lbrace>q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>b\<cdot>c + !b\<cdot>c'\<lbrace>q\<rbrace>"
  by (simp, metis mult_assoc mult_distl mult_distr)

lemma consequence_rule: "\<lbrakk>test p; p \<le> p'; \<lbrace>p'\<rbrace>c\<lbrace>q'\<rbrace>; q' \<le> q; test q\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>c\<lbrace>q\<rbrace>"
  by (metis hoare_triple_def mult_onel mult_oner sequence_rule test_leq_mult_def)

lemma while_rule: "\<lbrace>p\<rbrace>c\<lbrace>p\<rbrace> \<Longrightarrow> \<lbrace>p\<rbrace>c\<^sup>*\<lbrace>p\<rbrace>"
  by (metis hoare_triple_def_var star_sim2)

end
end
