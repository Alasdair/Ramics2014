theory DRA_FolkTheorem
  imports DRA
begin

context dra_tests
begin

abbreviation preservation :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "preserve" 60) where
  "x preserve p \<equiv> test p \<and> p\<cdot>x\<cdot>p = p\<cdot>x \<and> !p\<cdot>x\<cdot>!p = !p\<cdot>x"

lemma preserve_iteration: "x preserve p \<Longrightarrow> p\<cdot>x\<^sup>\<infinity> \<le> (p\<cdot>x)\<^sup>\<infinity>\<cdot>p"
  by (metis iteration_sim order_refl)

lemma preserve_tests: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p preserve q"
  by (metis test2 test_comp_closed_var)

lemma preserve_test_closed: "\<lbrakk>test p; x preserve q\<rbrakk> \<Longrightarrow> p\<cdot>x preserve q"
  apply (auto, metis mult_assoc test_mult_comm_var)
  by (metis mult_assoc test_comp_closed_var test_mult_comm_var)

lemma preserve_add_closed: "\<lbrakk>x preserve p; y preserve p\<rbrakk> \<Longrightarrow> x + y preserve p"
  by (metis distrib_left distrib_right')

lemma preserve_mult_closed: "\<lbrakk>x preserve p; y preserve p\<rbrakk> \<Longrightarrow> x\<cdot>y preserve p"
  by (metis mult_assoc)

lemma preserve_var: "x preserve p \<Longrightarrow> p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<infinity> \<le> p\<cdot>(p\<cdot>x)\<^sup>\<infinity>"
proof -
  assume assms: "x preserve p"
  have "p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<infinity> = p + (p \<cdot>p \<cdot>x + p \<cdot>!p \<cdot>y)\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<infinity>"
    by (metis distrib_left iteration_unfoldl_distl mult_assoc)
  hence "p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<infinity> \<le> 1 + p\<cdot>x\<cdot>p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<infinity>"
    by (metis assms annil test_comp_mult add_zeror test_mult_idem_var add_iso asg)
  hence "p\<cdot>(p\<cdot>x + !p\<cdot>y)\<^sup>\<infinity> \<le> (p\<cdot>x)\<^sup>\<infinity>"
    by (metis iteration_inductl mult_1_right mult_assoc)
  thus ?thesis 
    by (metis assms mult_assoc mult_isol test_mult_idem_var)
qed
  

lemma preserve_var2: "\<lbrakk>test p; test q; x preserve r; y preserve r\<rbrakk> \<Longrightarrow> (r\<cdot>p\<cdot>x + !r\<cdot>q\<cdot>y) preserve r"
proof -
  assume assms: "test p" "test q" "x preserve r" "y preserve r"
  have "r\<cdot>p\<cdot>x preserve r"
    by (smt assms(1) assms(3) mult_assoc preserve_test_closed test_comp_closed_var test_mult_idem_var)
  moreover have "!r\<cdot>q\<cdot>y preserve r"
    by (smt add_0_right assms(2) assms(4) mult_assoc preserve_test_closed test3 test_absorb2 test_def test_zero)
  ultimately show ?thesis
    by (metis preserve_add_closed)
qed


text {*
  We want to prove that every while program, suitably augmented with finitely many new subprograms 
  of the form s; bc + !b!c, is equivalent to a while program of the form p; while b do q.
  This theorem is proved by induction over the structure of the program.
*}

text {* 
  For the conditional structure, we show that the programs of the form
    z; gh + !g!h
    if g then x1; while f1 do y1
         else x2; while f2 do y2
  are equivalent to
    z; gh+ !g!h
    if g then x1 else x2; while hf1 + !hf2 do if h then y1 else y2
*}

lemma conditional_helper1: 
  assumes "test g" "test f1" "test f2"
          "x1 preserve h" "y1 preserve h"
          "x2 preserve h" "y2 preserve h"
  shows "g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1  \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1"
proof -
  have "g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1 \<le> g\<cdot>h\<cdot>x1\<cdot>h\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1"
    by (metis assms(4) eq_iff mult_assoc)
  also have "... \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1)\<^sup>\<infinity>\<cdot>h\<cdot>!f1"
    apply (subgoal_tac "f1\<cdot>y1 preserve h", metis preserve_iteration mult_assoc mult_isol mult_isor)
    by (metis assms(2) assms(5) preserve_test_closed)
  also have "... \<le>  g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1"
    by (metis iteration_subdist mult_assoc mult_double_iso)
  finally show ?thesis .
qed

lemma conditional_helper2:
  assumes "test g" "test f1" "test f2"
          "x1 preserve h" "y1 preserve h"
          "x2 preserve h" "y2 preserve h"
  shows "g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 \<le> g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1"
proof -
  have "g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 \<le> g\<cdot>h\<cdot>x1\<cdot>h\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!f1"
    by (metis assms(4) eq_refl mult_assoc mult_isol test_eq1 mult_assoc)
  also have "... \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2))\<^sup>\<infinity>\<cdot>h\<cdot>!f1"
    apply (subgoal_tac "h\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity> \<le> (h\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2))\<^sup>\<infinity>\<cdot>h")
    apply (metis less_eq_def mult_assoc mult_isor subdistl)
    by (metis assms(2-) preserve_var2 preserve_iteration)
  also have "... \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1"
    by (metis assms(5) distrib_left mult_assoc annil test_comp_mult add_0_right test_mult_idem_var eq_refl mult_assoc mult_isol test_eq1)
  also have "... \<le> g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1"
    by (metis assms(5) iteration_iso mult_assoc mult_double_iso mult_isol order_refl test_eq1)
  finally have step1: "g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 \<le> g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1" .
  have pres: "h\<cdot>f1\<cdot>y1 preserve h"
    by (smt assms mult_assoc preserve_test_closed test_comp_closed_var test_mult_idem_var)
  have "g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 \<le> g\<cdot>h\<cdot>x1\<cdot>h\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2"
    by (metis assms(4) eq_refl mult_assoc mult_assoc)
  also have "... \<le>  g\<cdot>h\<cdot>x1\<cdot>h\<cdot>(h\<cdot>f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2"
    by (smt pres preserve_var mult_assoc mult_double_iso test_comp_closed_var test_mult_idem_var)
  also have "... \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1)\<^sup>\<infinity>\<cdot>h\<cdot>!h\<cdot>!f2"
    by (metis pres eq_refl iteration_slide mult_assoc test_mult_idem_var)
  also have "... \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1)\<^sup>\<infinity>\<cdot>0\<cdot>!f2"
    by (metis assms(5) mult_assoc order_refl test_double_comp_var test_mult_comp)
  also have "... \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1"
    by (metis annil mult_assoc mult_isol zero_least)
  also have "... \<le> g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1"
    by (metis assms(5) iteration_iso mult_assoc mult_double_iso mult_isol order_refl test_eq1)
  finally have step2: "g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 \<le> g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1" .
  show ?thesis using step1 and step2 
    by (metis add_lub step1 step2)
qed
  
theorem conditional: 
  assumes assms: "test g" "test f1" "test f2"
          "x1 preserve h" "y1 preserve h"
          "x2 preserve h" "y2 preserve h"
  shows "g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(f2 \<cdot>y2)\<^sup>\<infinity>\<cdot>!f2 = (g\<cdot>h\<cdot>x1 + !g\<cdot>!h\<cdot>x2)\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>(h\<cdot>!f1 + !h\<cdot>!f2)"
proof -
  have "(g\<cdot>h\<cdot>x1 + !g\<cdot>!h\<cdot>x2)\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>(h\<cdot>!f1 + !h\<cdot>!f2) = g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>(h\<cdot>!f1 + !h\<cdot>!f2) + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>(h\<cdot>!f1 + !h\<cdot>!f2)"
    by (metis distrib_right')
  also have a: "... = g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2"
    by (metis distrib_left mult_assoc add_assoc)
  finally have rhs: "(g\<cdot>h\<cdot>x1 + !g\<cdot>!h\<cdot>x2)\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>(h\<cdot>!f1 + !h\<cdot>!f2) 
    = g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2" .

  have "g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(f2 \<cdot>y2)\<^sup>\<infinity>\<cdot>!f2 \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2"
    apply (subgoal_tac "g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1  \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1")
    apply (subgoal_tac "!g\<cdot>!h\<cdot>x2\<cdot>(f2 \<cdot>y2)\<^sup>\<infinity>\<cdot>!f2 \<le> !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2")
    by (metis add_iso_var, smt conditional_helper1 add_commute assms test_def, metis assms conditional_helper1)
  also have "... \<le> g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2"
    by (smt add_lub add_ub2 less_eq_def)
  finally have step1: "g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(f2 \<cdot>y2)\<^sup>\<infinity>\<cdot>!f2  \<le> (g\<cdot>h\<cdot>x1 + !g\<cdot>!h\<cdot>x2)\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>(h\<cdot>!f1 + !h\<cdot>!f2)"
    by (metis rhs)

  have "g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 \<le> g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(f2 \<cdot>y2)\<^sup>\<infinity>\<cdot>!f2"
    apply (subgoal_tac "g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + g\<cdot>h\<cdot>x1\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 \<le> g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1")
    apply (subgoal_tac "!g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>h\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!h\<cdot>!f2 \<le> !g\<cdot>!h\<cdot>x2\<cdot>(f2\<cdot>y2)\<^sup>\<infinity>\<cdot>!f2")
    apply (metis (full_types) a add_iso_var distrib_left mult_assoc)
    by (smt conditional_helper2 add_commute assms test_def, metis assms conditional_helper2)
  hence step2: "(g\<cdot>h\<cdot>x1 + !g\<cdot>!h\<cdot>x2)\<cdot>(h\<cdot>f1\<cdot>y1 + !h\<cdot>f2\<cdot>y2)\<^sup>\<infinity>\<cdot>(h\<cdot>!f1 + !h\<cdot>!f2) \<le> g\<cdot>h\<cdot>x1\<cdot>(f1\<cdot>y1)\<^sup>\<infinity>\<cdot>!f1 + !g\<cdot>!h\<cdot>x2\<cdot>(f2 \<cdot>y2)\<^sup>\<infinity>\<cdot>!f2" by (metis rhs)
  
  show ?thesis using step1 and step2
    by (metis eq_iff)
qed

text {* 
  For nested loops, we show that the programs of the form
    while b do (p; while c do q)
  are equivalent to
    if b then (p; while (b\<or>c) do (if c then q else p)) 
*}

theorem nested_loops:
  assumes "test f" "test g"
  shows "(f\<cdot>x\<cdot>(g\<cdot>y)\<^sup>\<infinity>\<cdot>!g)\<^sup>\<infinity>\<cdot>!f = f\<cdot>x\<cdot>(g\<cdot>y + !g\<cdot>f\<cdot>x)\<^sup>\<infinity>\<cdot>!f\<cdot>!g + !f"
proof -
  have "(g\<cdot>y + !g\<cdot>f\<cdot>x)\<^sup>\<infinity>\<cdot>!f\<cdot>!g = (g\<cdot>y)\<^sup>\<infinity>\<cdot>(!g\<cdot>f\<cdot>x\<cdot>(g\<cdot>y)\<^sup>\<infinity>)\<^sup>\<infinity>\<cdot>!f\<cdot>!g"
    by (metis iteration_denest)
  also have "... = (g\<cdot>y)\<^sup>\<infinity>\<cdot>(!g\<cdot>f\<cdot>x\<cdot>(g\<cdot>y)\<^sup>\<infinity>)\<^sup>\<infinity>\<cdot>!g\<cdot>!f"
    by (metis assms(1) assms(2) mult_assoc test_comp_closed_var test_mult_comm_var)
  also have "... = (g\<cdot>y)\<^sup>\<infinity>\<cdot>!g\<cdot>(f\<cdot>x\<cdot>(g\<cdot>y)\<^sup>\<infinity>\<cdot>!g)\<^sup>\<infinity>\<cdot>!f"
    by (metis iteration_slide mult_assoc)
  finally have "(g\<cdot>y + !g\<cdot>f\<cdot>x)\<^sup>\<infinity>\<cdot>!f\<cdot>!g = (g\<cdot>y)\<^sup>\<infinity>\<cdot>!g\<cdot>(f\<cdot>x\<cdot>(g\<cdot>y)\<^sup>\<infinity>\<cdot>!g)\<^sup>\<infinity>\<cdot>!f" .
  thus ?thesis
    by (metis mult_assoc add_comm iteration_unfoldl_distr)
qed

text {* 
  For postcomputation, we show that the programs of the form
    while b do p; q
  are equivalent to assuming without loss of generality that b and q commute
    if !b then q else while b do (p; if !b the q)) 
*}

lemma postcomputation:
  assumes "y preserve g"
  shows "(g\<cdot>x)\<^sup>\<infinity>\<cdot>!g\<cdot>y = !g\<cdot>y + g\<cdot>(g\<cdot>x\<cdot>(!g\<cdot>y + g))\<^sup>\<infinity>\<cdot>!g"
proof (rule antisym)
  have "g\<cdot>x\<cdot>(g\<cdot>x)\<^sup>\<infinity>\<cdot>!g\<cdot>y \<le> g\<cdot>x\<cdot>((!g\<cdot>y + g)\<cdot>g\<cdot>x)\<^sup>\<infinity>\<cdot>!g\<cdot>y\<cdot>!g"
    by (metis assms mult_assoc test_mult_idem_var add_commute add_ub1 iteration_iso mult_double_iso mult_isor)
  also have "... \<le> g\<cdot>x\<cdot>((!g\<cdot>y + g)\<cdot>g\<cdot>x)\<^sup>\<infinity>\<cdot>(!g\<cdot>y + g)\<cdot>!g"
    by (metis mult_assoc mult_isor subdistl)
  also have "... \<le> g\<cdot>!g + g\<cdot>g\<cdot>x\<cdot>(!g\<cdot>y + g)\<cdot>(g\<cdot>x\<cdot>(!g\<cdot>y + g))\<^sup>\<infinity>\<cdot>!g"
    by (metis assms iteration_slide mult_assoc test_mult_idem_var add_ub2)
  finally have "g\<cdot>x\<cdot>(g\<cdot>x)\<^sup>\<infinity>\<cdot>!g\<cdot>y \<le> g\<cdot>(g\<cdot>x\<cdot>(!g\<cdot>y + g))\<^sup>\<infinity>\<cdot>!g"
    by (smt distrib_left distrib_right' mult_assoc mult_onel mult_oner iteration_unfoldl)
  moreover have "(g\<cdot>x)\<^sup>\<infinity>\<cdot>!g\<cdot>y = !g\<cdot>y + g\<cdot>x\<cdot>(g\<cdot>x)\<^sup>\<infinity>\<cdot>!g\<cdot>y"
    by (metis iteration_unfoldl_distr mult_assoc)
  ultimately show "(g\<cdot>x)\<^sup>\<infinity>\<cdot>!g\<cdot>y \<le> !g\<cdot>y + g\<cdot>(g\<cdot>x\<cdot>(!g\<cdot>y + g))\<^sup>\<infinity>\<cdot>!g"
    by (smt add_assoc order_prop)
next
  let ?K = "(g\<cdot>x\<cdot>!g\<cdot>y + g\<cdot>x\<cdot>g)\<^sup>\<infinity>\<cdot>!g"
  have "g\<cdot>x\<cdot>!g\<cdot>y = g\<cdot>x\<cdot>!g\<cdot>y\<cdot>?K"
    by (metis assms mult_assoc test_iteration_annir distrib_left mult_assoc)
  hence "g\<cdot>x\<cdot>(!g\<cdot>y + g\<cdot>?K) = g\<cdot>g\<cdot>x\<cdot>!g\<cdot>y\<cdot>?K + g\<cdot>g\<cdot>x\<cdot>g\<cdot>?K + g\<cdot>!g"
    by (smt distrib_left mult_assoc assms test_mult_idem_var add_0_left add_commute test_comp_mult)
  hence "g\<cdot>x\<cdot>(!g\<cdot>y + g\<cdot>?K) = g\<cdot>(g\<cdot>x\<cdot>(!g\<cdot>y + g))\<^sup>\<infinity>\<cdot>!g"
    by (smt distrib_left distrib_right' mult_assoc mult_onel add_comm  iteration_unfoldl)
  thus "!g\<cdot>y + g\<cdot>(g\<cdot>x\<cdot>(!g\<cdot>y + g))\<^sup>\<infinity>\<cdot>!g \<le> (g\<cdot>x)\<^sup>\<infinity>\<cdot>!g\<cdot>y"
    by (metis iteration_inductl distrib_left mult_assoc order_refl)
qed

text {* 
  For composition, we show that the programs of the form
    while b do p; while c do q
  are equivalent to 
    if !b then while c do q else while b do (p; if !b then while c do q)
*}

lemma composition_helper: 
  assumes "test g" "test h" "g\<cdot>y = y\<cdot>g"
  shows "g\<cdot>(h\<cdot>y)\<^sup>\<infinity>\<cdot>!h\<cdot>g = g\<cdot>(h\<cdot>y)\<^sup>\<infinity>\<cdot>!h"
  apply (subgoal_tac "g\<cdot>(h\<cdot>y)\<^sup>\<infinity>\<cdot>!h \<le> (h\<cdot>y)\<^sup>\<infinity>\<cdot>!h\<cdot>g")
  apply (metis assms(1) test_eq3 mult_assoc)
  by (metis assms mult_assoc test_mult_comm_var order_refl iteration_sim mult_isor test_comp_closed_var)

theorem composition:
  assumes "test g" "test h" "g\<cdot>y = y\<cdot>g" "!g\<cdot>y = y\<cdot>!g"
  shows "(g\<cdot>x)\<^sup>\<infinity>\<cdot>!g\<cdot>(h\<cdot>y)\<^sup>\<infinity>\<cdot>!h = !g\<cdot>(h\<cdot>y)\<^sup>\<infinity>\<cdot>!h + g\<cdot>(g\<cdot>x\<cdot>(!g\<cdot>(h\<cdot>y)\<^sup>\<infinity>\<cdot>!h + g))\<^sup>\<infinity>\<cdot>!g"
  apply (subgoal_tac "(h\<cdot>y)\<^sup>\<infinity>\<cdot>!h preserve g")
  by (metis postcomputation mult_assoc, metis assms composition_helper test_comp_closed_var mult_assoc)  
  

end

end
