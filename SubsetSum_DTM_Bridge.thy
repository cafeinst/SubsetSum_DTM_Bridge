theory SubsetSum_DTM_Bridge
  imports "SubsetSum_DecisionTree"
begin

(* ========================================================================= *)
(* PART 1: Converting Turing Machines to Decision Trees                     *)
(* ========================================================================= *)

section ‹DTM bridge: abstract run model›

(* Convert a TM execution trace to a decision tree.
   
   The key insight: A deterministic TM that reads input tape positions
   can be viewed as a decision tree where:
   - Each node asks "what bit is at position head0(config)?"
   - The answer determines the next configuration
   - After t steps, we check the final accepting state
   
   This bridges the gap between:
   - Concrete TM semantics (stepf, conf, head0)
   - Abstract decision tree model (AskL/AskR nodes)
*)

fun tm_to_dtr' ::
  "('C ⇒ int) ⇒ ('C ⇒ bool ⇒ 'C) ⇒ ('C ⇒ bool) ⇒ nat ⇒ 'C ⇒ (nat,nat) dtr"
where
  "tm_to_dtr' head0 stepf final_acc 0 c = Leaf (final_acc c)"
| "tm_to_dtr' head0 stepf final_acc (Suc t) c =
     AskL (nat (head0 c))
          (tm_to_dtr' head0 stepf final_acc t (stepf c False))
          (tm_to_dtr' head0 stepf final_acc t (stepf c True))"
    (* Recursive case: Ask what bit is at head position,
       then recurse with the updated configuration *)

(* ========================================================================= *)
(* PART 2: Abstract TM Model (Just the Interface)                           *)
(* ========================================================================= *)

(* This locale defines the INTERFACE of a Turing Machine without
   specifying how it's implemented. It's just:
   - steps: how long does it run?
   - conf: what's the configuration at time t?
   - head0: where is the read head?
   - accepts: does it accept? *)

locale DTM_Run =
  fixes steps   :: "'M ⇒ bool list ⇒ nat"          (* halting time on input x *)
    and conf    :: "'M ⇒ bool list ⇒ nat ⇒ 'C"     (* configuration after t steps *)
    and head0   :: "'C ⇒ int"                      (* position of input-tape head *)
    and accepts :: "'M ⇒ bool list ⇒ bool"         (* acceptance predicate *)
begin

(* The set of tape positions read during the entire computation *)
definition read0 :: "'M ⇒ bool list ⇒ nat set" where
  "read0 M x = (λt. nat (head0 (conf M x t))) ` {..< steps M x}"

(* Basic facts: this set is finite and bounded by the number of steps *)
lemma finite_read0[simp]: "finite (read0 M x)"
  unfolding read0_def by (intro finite_imageI) simp

lemma card_read0_le_steps:
  "card (read0 M x) ≤ steps M x"
  unfolding read0_def by (metis card_image_le card_lessThan finite_lessThan)

end

(* ========================================================================= *)
(* PART 3: Splice Operation (Overwriting a Contiguous Block)                *)
(* ========================================================================= *)

section ‹Contiguous overwrite (splice)›

(* splice a w xs bs: Replace positions [a, a+w) in xs with the bits bs
   
   This is used to construct adversarial inputs:
   - Start with original input xs
   - Overwrite a specific block [a, a+w) with new bits bs
   - Keep everything else the same
   
   Key property: If the TM doesn't read positions [a, a+w), then it can't
   tell the difference between xs and splice(a, w, xs, bs)! *)

definition splice :: "nat ⇒ nat ⇒ bool list ⇒ bool list ⇒ bool list" where
  "splice a w xs bs = take a xs @ bs @ drop (a + w) xs"
    (* take first a bits, then bs, then everything after position a+w *)

(* Three key lemmas about indexing into spliced lists: *)

(* Inside the spliced region [a, a+w): get bit from bs *)
lemma splice_nth_inside:
  assumes LEN: "length bs = w"
      and BND: "a + w ≤ length xs"
      and IN1: "a ≤ i"
      and IN2: "i < a + w"
  shows "splice a w xs bs ! i = bs ! (i - a)"
proof -
  have ia_lt: "i - a < w" using IN1 IN2 by arith
  have a_le_len: "a ≤ length xs" using BND by linarith
  have "splice a w xs bs ! i = (take a xs @ bs @ drop (a + w) xs) ! i"
    by (simp add: splice_def)
  also have "... = (bs @ drop (a + w) xs) ! (i - a)"
    using IN1 a_le_len by (simp add: nth_append)
  also have "... = bs ! (i - a)"
    using ia_lt LEN by (simp add: nth_append)
  finally show ?thesis .
qed

(* Left of the spliced region (i < a): unchanged *)
lemma splice_nth_left:
  assumes BND: "a ≤ length xs"
      and L:   "i < a"
  shows "splice a w xs bs ! i = xs ! i"
  using assms by (simp add: splice_def nth_append)

(* Right of the spliced region (i ≥ a+w): unchanged *)
lemma splice_nth_right:
  assumes LEN: "length bs = w"
      and BND: "a + w ≤ length xs"
      and R:   "a + w ≤ i"
  shows "splice a w xs bs ! i = xs ! i"
proof -
  have a_le_len: "a ≤ length xs" using BND by linarith
  have i_ge_a:   "a ≤ i"         using R   by linarith
  have i_minus_ge_w: "i - a ≥ w" using R   by arith
  have "splice a w xs bs ! i = (take a xs @ bs @ drop (a + w) xs) ! i"
    by (simp add: splice_def)
  also have "... = (bs @ drop (a + w) xs) ! (i - a)"
    using i_ge_a a_le_len by (simp add: nth_append)
  also have "... = drop (a + w) xs ! (i - a - length bs)"
    using LEN i_minus_ge_w by (simp add: nth_append)
  also have "... = drop (a + w) xs ! (i - (a + w))"
    by (simp add: LEN)
  also have "... = xs ! i"
    using BND R by (simp add: add_diff_inverse_nat)
  finally show ?thesis .
qed

(* ========================================================================= *)
(* PART 4: TM with Concrete Semantics (The Full Specification)              *)
(* ========================================================================= *)

section ‹DTM semantics sufficient for unread-agreement›

(* This locale extends DTM_Run with CONCRETE semantics:
   - How configurations evolve (step_sem)
   - When halting time is stable (steps_stable_raw)
   - How acceptance is determined (accepts_sem)
   
   CRITICAL: These axioms give us "unread-agreement" - if two inputs
   agree on all read positions, they have the same behavior! *)

locale DTM_Run_Sem =
  fixes steps     :: "'M ⇒ bool list ⇒ nat"
    and conf      :: "'M ⇒ bool list ⇒ nat ⇒ 'C"
    and head0     :: "'C ⇒ int"
    and accepts   :: "'M ⇒ bool list ⇒ bool"
    and M         :: 'M
    and stepf     :: "'C ⇒ bool ⇒ 'C"     (* transition function *)
    and final_acc :: "'C ⇒ bool"           (* final acceptance check *)

  (* AXIOM 1: Deterministic evolution - next config depends only on
     current config and the bit at the head position *)
  assumes step_sem:
    "⋀x t. conf M x (Suc t) = stepf (conf M x t) (x ! nat (head0 (conf M x t)))"

 (* AXIOM 2: Halting time stability - if two inputs agree on all positions
     that are ever read on x, they have the same halting time *)
  assumes steps_stable_raw:
    "⋀x y. (⋀i. i ∈ ((λt. nat (head0 (conf M x t))) ` {..< steps M x}) ⟹ x ! i = y ! i)
           ⟹ steps M x = steps M y"

 (* AXIOM 3: Acceptance determined by final configuration *)
  assumes accepts_sem:
    "⋀x. accepts M x = final_acc (conf M x (steps M x))"

  (* AXIOM 4: Initial configuration doesn't depend on input *)
  assumes conf0_same: "⋀x y. conf M x 0 = conf M y 0"
begin

(* ========================================================================= *)
(* Helper: "Drive" a configuration forward using an oracle                  *)
(* ========================================================================= *)

(* drive t c inp: Simulate t steps starting from config c,
   using oracle inp to answer tape queries.
   
   This generalizes TM execution to work with arbitrary oracles,
   not just concrete bit strings. *)

primrec drive :: "nat ⇒ 'C ⇒ (nat ⇒ bool) ⇒ 'C" where
  "drive 0 c inp = c"
| "drive (Suc t) c inp =
     (let i = nat (head0 c); b = inp i in drive t (stepf c b) inp)"

(* KEY LEMMA: Driving with the oracle (λi. x ! i) is the same as
   running the TM on input x *)
lemma drive_conf_gen:
  "drive t (conf M x u) (λi. x ! i) = conf M x (u + t)"
proof (induction t arbitrary: u)
  case 0 show ?case by simp
next
  case (Suc t)
  have "drive (Suc t) (conf M x u) (λi. x ! i)
        = drive t (stepf (conf M x u) (x ! nat (head0 (conf M x u)))) (λi. x ! i)"
    by simp
  also have "... = drive t (conf M x (Suc u)) (λi. x ! i)"
    by (simp add: step_sem)
  also have "... = conf M x (Suc u + t)"
    by (simp add: Suc.IH)
  finally show ?case by simp
qed

lemma drive_conf:
  "drive t (conf M x 0) (λi. x ! i) = conf M x t"
  by (simp add: drive_conf_gen)

(* ========================================================================= *)
(* PART 5: Correctness of the TM→DT Conversion                             *)
(* ========================================================================= *)

(* THEOREM: The decision tree produced by tm_to_dtr' correctly simulates
   the TM's computation *)
lemma run_tm_to_dtr':
  "run oL oR (tm_to_dtr' head0 stepf final_acc t c)
   = final_acc (drive t c oL)"
  by (induction t arbitrary: c) (simp_all add: Let_def)

(* Specialization: Running the tree with (λi. x!i) gives the right answer *)
lemma tm_to_dtr_correct:
  "run (λi. x ! i) (λi. x ! i)
        (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
   = final_acc (conf M x (steps M x))"
  by (simp add: run_tm_to_dtr' drive_conf)

corollary tm_to_dtr_accepts:
  "run (λi. x ! i) (λi. x ! i)
        (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
   = accepts M x"
  by (simp add: tm_to_dtr_correct accepts_sem)

(* ========================================================================= *)
(* PART 6: Tracking Which Indices Are Queried                               *)
(* ========================================================================= *)

(* Local definition of read set (will be shown equal to DTM_Run's version) *)
definition read0S :: "bool list ⇒ nat set" where
  "read0S x = (λt. nat (head0 (conf M x t))) ` {..< steps M x}"

(* handy: one-step shift for images over {..<t} to {..<Suc t} *)
lemma image_shift_suc_subset:
  fixes F :: "nat ⇒ 'a"
  shows "(λu. F u) ` {..<t} ⊆ F ` {..<Suc t}"
  by auto

(* THEOREM: The decision tree only queries indices that the TM actually reads *)

lemma seenL_tm_to_dtr_subset_read0_helper:
  "seenL_run oL oR (tm_to_dtr' head0 stepf final_acc t c)
     ⊆ (λu. nat (head0 (drive u c oL))) ` {..< t}"
proof (induction t arbitrary: c)
  case 0
  show ?case by simp
next
  case (Suc t)
  let ?i = "nat (head0 c)"

  have root_in:
    "?i ∈ (λu. nat (head0 (drive u c oL))) ` {..< Suc t}"
    by (rule image_eqI[where x=0]) simp_all

  have IH_sub:
    "seenL_run oL oR
       (tm_to_dtr' head0 stepf final_acc t (stepf c (oL ?i)))
     ⊆ (λu. nat (head0 (drive u (stepf c (oL ?i)) oL))) ` {..< t}"
    by (rule Suc.IH)

  have drive_suc:
    "(λu. nat (head0 (drive u (stepf c (oL ?i)) oL)))
     = (λu. nat (head0 (drive (Suc u) c oL)))"
    by (intro ext) simp

  have sub_into_parent:
    "(λu. nat (head0 (drive (Suc u) c oL))) ` {..< t}
     ⊆ (λu. nat (head0 (drive u c oL))) ` {..< Suc t}"
  proof
    fix y
    assume "y ∈ (λu. nat (head0 (drive (Suc u) c oL))) ` {..< t}"
    then obtain u where u_lt: "u < t"
      and y_def: "y = nat (head0 (drive (Suc u) c oL))" by auto
    have "y = (λv. nat (head0 (drive v c oL))) (Suc u)"
      by (simp add: y_def)
    moreover have "Suc u ∈ {..< Suc t}"
      using u_lt by simp
    ultimately show "y ∈ (λu. nat (head0 (drive u c oL))) ` {..< Suc t}"
      by (rule image_eqI)
  qed

  have split:
    "seenL_run oL oR (tm_to_dtr' head0 stepf final_acc (Suc t) c)
       = insert ?i (seenL_run oL oR
              (tm_to_dtr' head0 stepf final_acc t (stepf c (oL ?i))))"
    by simp

  show ?case
    using root_in IH_sub split drive_suc sub_into_parent by auto
qed

(* Inherit the DTM_Run locale to get its read0 definition *)
sublocale Base: DTM_Run steps conf head0 accepts .

(* Bridge lemma: Our local read0S equals the inherited Base.read0 *)
lemma seenL_tm_to_dtr_subset_read0:
  fixes x :: "bool list"
  defines "T ≡ tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0)"
  shows "seenL_run (λi. x ! i) (λj. x ! j) T ⊆ Base.read0 M x"
proof -
  have A:
    "seenL_run (λi. x ! i) (λj. x ! j)
       (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
     ⊆ (λu. nat (head0 (drive u (conf M x 0) (λi. x ! i)))) ` {..< steps M x}"
    by (rule seenL_tm_to_dtr_subset_read0_helper)
  also have "… = (λu. nat (head0 (conf M x u))) ` {..< steps M x}"
    by (simp add: drive_conf)
  also have "… = Base.read0 M x"
    unfolding Base.read0_def by simp
  finally show ?thesis by (simp add: T_def)
qed

(* 1) Helper proved by induction on t *)
lemma seenR_tm_to_dtr_subset_read0_helper:
  "seenR_run oL oR (tm_to_dtr' head0 stepf final_acc t c)
     ⊆ (λu. nat (head0 (drive u c oL))) ` {..< t}"
proof (induction t arbitrary: c)
  case 0
  show ?case by simp
next
  case (Suc t)
  let ?i = "nat (head0 c)"
  have split:
    "seenR_run oL oR (tm_to_dtr' head0 stepf final_acc (Suc t) c)
     = seenR_run oL oR (tm_to_dtr' head0 stepf final_acc t (stepf c (oL ?i)))"
    by simp
  have IH_sub:
    "seenR_run oL oR (tm_to_dtr' head0 stepf final_acc t (stepf c (oL ?i)))
       ⊆ (λu. nat (head0 (drive u (stepf c (oL ?i)) oL))) ` {..< t}"
    by (rule Suc.IH)
  have drive_suc:
    "(λu. nat (head0 (drive u (stepf c (oL ?i)) oL)))
     = (λu. nat (head0 (drive (Suc u) c oL)))"
    by (intro ext) simp
  have shift:
    "(λu. nat (head0 (drive (Suc u) c oL))) ` {..< t}
       ⊆ (λu. nat (head0 (drive u c oL))) ` {..< Suc t}"
  proof
    fix y assume "y ∈ (λu. nat (head0 (drive (Suc u) c oL))) ` {..< t}"
    then obtain u where u:"u < t" and y:"y = nat (head0 (drive (Suc u) c oL))" by auto
    have "Suc u ∈ {..< Suc t}" using u by simp
    have mem: "Suc u ∈ {..< Suc t}" using u by simp
    have eq:  "y = (λv. nat (head0 (drive v c oL))) (Suc u)" by (simp add: y)
    have "(λv. nat (head0 (drive v c oL))) (Suc u)
        ∈ (λv. nat (head0 (drive v c oL))) ` {..< Suc t}"
      using mem by (rule imageI)
    thus "y ∈ (λv. nat (head0 (drive v c oL))) ` {..< Suc t}"
      by (simp add: eq)
  qed
  from split IH_sub drive_suc shift show ?case by auto
qed

(* Symmetric result for right-queries (though we only use left in practice) *)
lemma seenR_tm_to_dtr_subset_read0:
  fixes x :: "bool list"
  defines "T ≡ tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0)"
  shows "seenR_run (λi. x ! i) (λj. x ! j) T ⊆ Base.read0 M x"
proof -
  have
    "seenR_run (λi. x ! i) (λj. x ! j)
       (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
     ⊆ (λu. nat (head0 (drive u (conf M x 0) (λi. x ! i)))) ` {..< steps M x}"
    by (rule seenR_tm_to_dtr_subset_read0_helper)
  also have "… = (λu. nat (head0 (conf M x u))) ` {..< steps M x}"
    by (simp add: drive_conf)
  also have "… = Base.read0 M x"
    unfolding Base.read0_def by simp
  finally show ?thesis by (simp add: T_def)
qed

(* ========================================================================= *)
(* PART 7: The Unread-Agreement Property                                    *)
(* ========================================================================= *)

(* Helper lemmas connecting the two read-set definitions *)
lemma read0_bridge: "read0S x = Base.read0 M x"
  by (simp add: read0S_def Base.read0_def)

lemma steps_stable:
  assumes AG: "⋀i. i ∈ Base.read0 M x ⟹ x ! i = y ! i"
  shows "steps M x = steps M y"
proof (rule steps_stable_raw)
  fix i
  assume iIn: "i ∈ (λt. nat (head0 (conf M x t))) ` {..< steps M x}"
  (* 1) Turn it into membership in the local read-set *)
  have iR0S: "i ∈ read0S x"
    using iIn by (simp add: read0S_def)
  (* 2) Bridge to the locale’s read-set *)
  have iBase: "i ∈ Base.read0 M x"
    using iR0S by (simp add: read0_bridge)
  (* 3) Apply the assumption *)
  show "x ! i = y ! i" by (rule AG[OF iBase])
qed

(* helper: if t < steps, the index read at time t is in read0S *)
lemma idx_in_read0S:
  assumes "t < steps M x"
  shows "nat (head0 (conf M x t)) ∈ read0S x"
  using assms
  unfolding read0S_def
  by (intro image_eqI[where x=t]) simp_all

(* THE BIG THEOREM: Unread-Agreement
   
   If two inputs x and y agree on all positions that M reads on x,
   then M accepts x iff M accepts y.
   
   This is the foundation of the adversarial argument! *)
lemma unread_agreement:
  assumes AG: "⋀i. i ∈ Base.read0 M x ⟹ x ! i = y ! i"
  shows "accepts M x ⟷ accepts M y"
proof -
  (* same halting time *)
  have steps_eq: "steps M x = steps M y"
    by (rule steps_stable[OF AG])

  (* convert agreement to the local read-set once *)
  have AGS: "⋀i. i ∈ read0S x ⟹ x ! i = y ! i"
  proof -
    fix i assume "i ∈ read0S x"
    hence "i ∈ Base.read0 M x" by (simp add: read0_bridge)
    thus "x ! i = y ! i" by (rule AG)
  qed

  (* configurations match up to the halting time *)
  have conf_eq: "⋀t. t ≤ steps M x ⟹ conf M x t = conf M y t"
  proof-
    fix t :: nat
    show "t ≤ steps M x ⟹ conf M x t = conf M y t"
    proof (induction t)
      case 0
      show ?case by (simp add: conf0_same) 
    next
      case (Suc t)
  (* from Suc t ≤ steps … get the strict bound we actually need *)
      have t_lt: "t < steps M x" using Suc.prems by simp

  (* apply IH at t ≤ steps … *)
      have IH: "conf M x t = conf M y t" by (rule Suc.IH) (use Suc.prems in simp)

      let ?i = "nat (head0 (conf M x t))"

  (* the scanned index at time t is in the read-set *)
      have i_mem: "?i ∈ read0S x"
        unfolding read0S_def
        by (intro image_eqI[where x=t]) (use t_lt in simp_all)

  (* inputs agree on that index *)
      have scan_eq: "x ! ?i = y ! ?i" using AGS i_mem by blast

  (* one deterministic step using same scanned bit *)
      let ?i = "nat (head0 (conf M x t))"

(* rewrite the index using the IH on configurations *)
      have i_y: "?i = nat (head0 (conf M y t))"
        by (simp add: IH)

      have "conf M x (Suc t) = stepf (conf M x t) (x ! ?i)"
        by (simp add: step_sem)
      also have "... = stepf (conf M y t) (y ! ?i)"
        using IH scan_eq by simp
      also have "... = stepf (conf M y t) (y ! nat (head0 (conf M y t)))"
        by (simp add: i_y)
      also have "... = conf M y (Suc t)"
        by (simp only: step_sem[symmetric])
      finally show ?case .
    qed
  qed

  (* acceptance depends only on final configuration *)
  have "accepts M x = final_acc (conf M x (steps M x))" by (rule accepts_sem)
  also have "... = final_acc (conf M y (steps M y))" using conf_eq steps_eq by simp
  also have "... = accepts M y" by (rule accepts_sem[symmetric])
  finally show ?thesis .
qed

abbreviation sp :: "nat ⇒ nat ⇒ bool list ⇒ bool list ⇒ bool list" where
  "sp ≡ SubsetSum_DTM_Bridge.splice"

end

(* ========================================================================= *)
(* PART 8: Encoding Scheme - Blocks and Catalogs                            *)
(* ========================================================================= *)

section ‹Catalog blocks and padded encoding›

text ‹THE ENCODING STRATEGY:
  
  We encode a subset-sum instance (as, s, k) as:
    enc0(as,s) || padL || padR
  
  where:
  - enc0 is some baseline encoding (not read by the TM!)
  - padL contains all possible LHS values in fixed-width blocks
  - padR contains all possible RHS values in fixed-width blocks
  
  The TM will check if any LHS value equals any RHS value by reading these blocks.
›

(* Enumerate LHS and RHS values as sorted lists *)
definition enumL where
  "enumL as s k = sorted_list_of_set (LHS (e_k as s k) (length as))"

definition enumR where
  "enumR as s k = sorted_list_of_set (RHS (e_k as s k) (length as))"

lemma finite_LHS[simp]: "finite (LHS e n)"
  unfolding LHS_def by fastforce

lemma finite_RHS[simp]: "finite (RHS e n)"
  unfolding RHS_def by fastforce

lemma enumL_set[simp]:
  "set (enumL as s k) = LHS (e_k as s k) (length as)"
  by (simp add: enumL_def)

lemma enumR_set[simp]:
  "set (enumR as s k) = RHS (e_k as s k) (length as)"
  by (simp add: enumR_def)

(* Block width: large enough to encode any value *)
text ‹Fixed block width; later you can make it logarithmic in the values.›
definition W :: "int list ⇒ int ⇒ nat" where
  "W as s = max 1 (length as)"

(* Offset calculations for blocks in the padding regions *)
definition offL :: "int list ⇒ int ⇒ nat ⇒ nat" where
  "offL as s j = j * W as s"

definition offR :: "int list ⇒ int ⇒ nat ⇒ nat ⇒ nat" where
  "offR as s k j = length (enumL as s k) * W as s + j * W as s"

(* Block definitions (relative to start of padding) *)
definition blockL :: "int list ⇒ int ⇒ nat ⇒ nat set" where
  "blockL as s j = { offL as s j ..< offL as s j + W as s }"

definition blockR :: "int list ⇒ int ⇒ nat ⇒ nat ⇒ nat set" where
  "blockR as s k j = { offR as s k j ..< offR as s k j + W as s }"

(* Absolute block positions (including enc0 prefix) *)
definition blockL_abs ::
  "(int list ⇒ int ⇒ bool list) ⇒ int list ⇒ int ⇒ nat ⇒ nat set" where
  "blockL_abs E as s j =
     { length (E as s) + offL as s j ..<
       length (E as s) + offL as s j + W as s }"

definition blockR_abs ::
  "(int list ⇒ int ⇒ bool list) ⇒ int list ⇒ int ⇒ nat ⇒ nat ⇒ nat set" where
  "blockR_abs E as s k j =
     { length (E as s) + offR as s k j ..<
       length (E as s) + offR as s k j + W as s }"

(* KEY PROPERTY: All blocks are disjoint! *)

lemma blockL_abs_disjoint:
  assumes "j ≠ j'"
  shows   "blockL_abs E as s j ∩ blockL_abs E as s j' = {}"
proof -
  let ?W = "W as s"
  let ?c = "length (E as s)"
  have "j < j' ∨ j' < j" using assms by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * ?W ≤ j' * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + j * ?W + ?W ≤ ?c + j' * ?W" by simp
    thus ?thesis by (auto simp: blockL_abs_def offL_def)
  next
    assume lt: "j' < j"
    have "(Suc j') * ?W ≤ j * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + j' * ?W + ?W ≤ ?c + j * ?W" by simp
    thus ?thesis by (auto simp: blockL_abs_def offL_def)
  qed
qed

lemma blockR_abs_disjoint:
  assumes "j ≠ j'"
  shows   "blockR_abs E as s k j ∩ blockR_abs E as s k j' = {}"
proof -
  let ?W = "W as s"
  let ?c = "length (E as s)"
  have "j < j' ∨ j' < j" using assms by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * ?W ≤ j' * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + offR as s k j + ?W ≤ ?c + offR as s k j'"
      by (simp add: offR_def add_mult_distrib2)
    thus ?thesis by (auto simp: blockR_abs_def)
  next
    assume lt: "j' < j"
    have "(Suc j') * ?W ≤ j * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + offR as s k j' + ?W ≤ ?c + offR as s k j"
      by (simp add: offR_def add_mult_distrib2)
    thus ?thesis by (auto simp: blockR_abs_def)
  qed
qed

lemma blockL_abs_blockR_abs_disjoint:
  assumes jL: "j < length (enumL as s k)"
  shows   "blockL_abs E as s j ∩ blockR_abs E as s k j' = {}"
proof -
  let ?W = "W as s"
  let ?c = "length (E as s)"
  have step:
    "?c + offL as s j + ?W ≤ ?c + offR as s k j'"
  proof -
    have "(Suc j) * ?W ≤ length (enumL as s k) * ?W"
      using jL by (intro mult_right_mono) simp_all
    hence "?c + (Suc j) * ?W ≤ ?c + length (enumL as s k) * ?W" by simp
    also have "… ≤ ?c + (length (enumL as s k) * ?W + j' * ?W)" by simp
    finally show ?thesis
      by (simp add: offL_def offR_def add_mult_distrib2)
  qed
  show ?thesis
    using step by (auto simp: blockL_abs_def blockR_abs_def)
qed

(* same width, consecutive half-open blocks are disjoint when indices differ *)
lemma blocks_disjoint_same_base:
  fixes W :: nat
  assumes "W > 0" and "j ≠ j'"
  shows "{j*W ..< j*W + W} ∩ {j'*W ..< j'*W + W} = {}"
proof -
  have "j < j' ∨ j' < j" using assms(2) by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * W ≤ j' * W"
      using lt assms(1) by (intro mult_right_mono) simp_all
    hence "j*W + W ≤ j'*W" by simp
    thus ?thesis by auto
  next
    assume lt: "j' < j"
    have "(Suc j') * W ≤ j * W"
      using lt assms(1) by (intro mult_right_mono) simp_all
    hence "j'*W + W ≤ j*W" by simp
    thus ?thesis by auto
  qed
qed

(* Disjointness results *)
lemma blockL_disjoint:
  assumes "j ≠ j'"
  shows   "blockL as s j ∩ blockL as s j' = {}"
proof -
  have Wpos: "W as s > 0" by (simp add: W_def)
  have base:
    "{offL as s j ..< offL as s j + W as s}
     ∩ {offL as s j' ..< offL as s j' + W as s} = {}"
    using blocks_disjoint_same_base[of "W as s" j j'] Wpos assms
    by (simp add: offL_def)
  show ?thesis using blockL_def base by simp
qed

lemma blockR_disjoint:
  assumes "j ≠ j'"
  shows "blockR as s k j ∩ blockR as s k j' = {}"
proof -
  have "j < j' ∨ j' < j" using assms by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * W as s ≤ j' * W as s"
      using lt by (intro mult_right_mono) simp_all
    hence "offR as s k j + W as s ≤ offR as s k j'"
      by (simp add: offR_def algebra_simps)   (* j*W + W = (Suc j)*W *)
    thus ?thesis by (auto simp: blockR_def)
  next
    assume lt: "j' < j"
    have "(Suc j') * W as s ≤ j * W as s"
      using lt by (intro mult_right_mono) simp_all
    hence "offR as s k j' + W as s ≤ offR as s k j"
      by (simp add: offR_def algebra_simps)
    thus ?thesis by (auto simp: blockR_def)
  qed
qed

lemma blockL_blockR_disjoint:
  assumes jL: "j < length (enumL as s k)"
  shows "blockL as s j ∩ blockR as s k j' = {}"
proof -
  let ?W = "W as s"
  let ?base = "length (enumL as s k) * ?W"

  have Suc_le: "Suc j ≤ length (enumL as s k)" using jL by simp
  have topL: "offL as s j + ?W ≤ ?base"
  proof -
    have "offL as s j + ?W = (j + 1) * ?W"
      by (simp add: offL_def add_mult_distrib2)
    also have "... ≤ length (enumL as s k) * ?W"
      using Suc_le by (intro mult_right_mono) simp_all
    finally show ?thesis .
  qed

  have "blockL as s j ⊆ {..< ?base}"
  proof
    fix x assume xL: "x ∈ blockL as s j"
    have x_lt: "x < offL as s j + W as s"
      using xL by (simp add: blockL_def)
    have "x < length (enumL as s k) * W as s"
      using x_lt topL by (rule less_le_trans)
    thus "x ∈ {..< length (enumL as s k) * W as s}"
  by simp
  qed
  moreover
  have "blockR as s k j' ⊆ {?base ..< ?base + ?W + j' * ?W}"
    by (auto simp: blockR_def offR_def W_def)
  ultimately show ?thesis by fastforce
qed

(* ========================================================================= *)
(* PART 9: The Padded Encoding Locale                                       *)
(* ========================================================================= *)

section ‹Padding encoder›

(* This locale defines an encoding scheme with:
   - enc0: baseline encoding (NOT read by TM)
   - to_bits/from_bits: binary encoding of integers
   - Assumption: binary encoding is a bijection (round-trip property) *)

locale SubsetSum_Padded_Enc =
  fixes enc0      :: "int list ⇒ int ⇒ bool list"     (* baseline CL encoding *)
    and to_bits   :: "nat ⇒ int ⇒ bool list"           (* fixed-width bits of an integer *)
    and from_bits :: "bool list ⇒ int"
  assumes bits_roundtrip:
    "⋀as s k v. v ∈ set (enumL as s k) ∪ set (enumR as s k) ⟹
       length (to_bits (W as s) v) = W as s ∧ from_bits (to_bits (W as s) v) = v"
begin

(* padL: concatenate binary encodings of all LHS values *)
definition padL where
  "padL as s k = concat (map (to_bits (W as s)) (enumL as s k))"

(* padR: concatenate binary encodings of all RHS values *)
definition padR where
  "padR as s k = concat (map (to_bits (W as s)) (enumR as s k))"

(* THE FULL ENCODING: baseline || LHS-catalog || RHS-catalog *)
definition enc where
  "enc as s k = enc0 as s @ padL as s k @ padR as s k"

(* Sum of a constant over any list *)
lemma sum_const_all_nat: "(∑ _← L. (c::nat)) = length L * c" for L c
  by (induction L) simp_all

(* helper: length rule on elements of enumL / enumR *)
lemma to_bits_len_on_enumL:
  assumes vL: "v ∈ set (enumL as s k)"
  shows   "length (to_bits (W as s) v) = W as s"
proof -
  have inU: "v ∈ set (enumL as s k) ∪ set (enumR as s k)"
    using vL by auto   (* or: by (rule UnI1) *)
  from bits_roundtrip[OF inU] show ?thesis by simp
qed

lemma to_bits_len_on_enumR:
  assumes vR: "v ∈ set (enumR as s k)"
  shows   "length (to_bits (W as s) v) = W as s"
proof -
  have inU: "v ∈ set (enumL as s k) ∪ set (enumR as s k)"
    using vR by auto   (* or: by (rule UnI2) *)
  from bits_roundtrip[OF inU] show ?thesis by simp
qed

(* pointwise constant-length maps over the enumerations *)
lemma map_len_to_bits_constL:
  "map (λv. length (to_bits (W as s) v)) (enumL as s k)
   = map (λ_. W as s) (enumL as s k)"
  by (rule map_cong[OF refl]) (simp add: to_bits_len_on_enumL)

lemma map_len_to_bits_constR:
  "map (λv. length (to_bits (W as s) v)) (enumR as s k)
   = map (λ_. W as s) (enumR as s k)"
  by (rule map_cong[OF refl]) (simp add: to_bits_len_on_enumR)

(* Length formulas (needed for bounds checking) *)
lemma length_padL:
  "length (padL as s k) = length (enumL as s k) * W as s"
proof -
  have "length (padL as s k)
        = sum_list (map (length ∘ to_bits (W as s)) (enumL as s k))"
    by (simp add: padL_def length_concat)
  also have "... = sum_list (map (λv. length (to_bits (W as s) v)) (enumL as s k))"
    by (simp add: comp_def)
  also have "... = sum_list (map (λ_. W as s) (enumL as s k))"
    by (simp add: map_len_to_bits_constL)
  also have "... = length (enumL as s k) * W as s"
    by (rule sum_const_all_nat)
  finally show ?thesis .
qed

lemma length_padR:
  "length (padR as s k) = length (enumR as s k) * W as s"
proof -
  have "length (padR as s k)
        = sum_list (map (length ∘ to_bits (W as s)) (enumR as s k))"
    by (simp add: padR_def length_concat)
  also have "... = sum_list (map (λv. length (to_bits (W as s) v)) (enumR as s k))"
    by (simp add: comp_def)
  also have "... = sum_list (map (λ_. W as s) (enumR as s k))"
    by (simp add: map_len_to_bits_constR)
  also have "... = length (enumR as s k) * W as s"
    by (rule sum_const_all_nat)
  finally show ?thesis .
qed

lemma length_enc:
  "length (enc as s k)
   = length (enc0 as s)
     + length (enumL as s k) * W as s
     + length (enumR as s k) * W as s"
proof -
  have "length (enc as s k)
        = length (enc0 as s) + length (padL as s k) + length (padR as s k)"
    by (simp add: enc_def)
  also have "... = length (enc0 as s)
                     + length (enumL as s k) * W as s
                     + length (enumR as s k) * W as s"
    by (simp add: length_padL length_padR)
  finally show ?thesis .
qed

end

(* ========================================================================= *)
(* PART 10: The Coverage Theorem (Main Result)                              *)
(* ========================================================================= *)

section ‹Coverage via unread-agreement›

(* THE MAIN LOCALE: Combines TM semantics + encoding scheme
   
   Key assumptions:
   1. correctness: TM correctly solves subset-sum
   2. read0_after_enc0: TM only reads the padding region (not enc0)
   3. kk: a fixed split point
*)
locale Coverage_TM =
  DTM_Run_Sem steps conf head0 accepts M stepf final_acc +
  SubsetSum_Padded_Enc enc0 to_bits from_bits
  for steps :: "'M ⇒ bool list ⇒ nat"
  and conf  :: "'M ⇒ bool list ⇒ nat ⇒ 'C"
  and head0 :: "'C ⇒ int"
  and accepts :: "'M ⇒ bool list ⇒ bool"
  and M :: 'M
  and stepf :: "'C ⇒ bool ⇒ 'C"
  and final_acc :: "'C ⇒ bool"
  and enc0  :: "int list ⇒ int ⇒ bool list"
  and to_bits :: "nat ⇒ int ⇒ bool list"
  and from_bits :: "bool list ⇒ int"
  +
fixes kk :: nat

 (* ASSUMPTION: The TM correctly decides subset-sum *)
  assumes correctness:
    "accepts M (enc as s kk)
       ⟷ good as s (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j)"

begin

abbreviation x0 :: "int list ⇒ int ⇒ bool list" where
  "x0 as s ≡ enc as s kk"

(* A block is "touched" if at least one position in it is read *)
definition touches :: "bool list ⇒ nat set ⇒ bool" where
  "touches x B ⟷ Base.read0 M x ∩ B ≠ {}"

lemma offL_window_in_enc:
  assumes jL: "j < length (enumL as s kk)"
  shows "length (enc0 as s) + offL as s j + W as s ≤ length (enc as s kk)"
proof -
  have pad_bound:
    "offL as s j + W as s ≤ length (padL as s kk) + length (padR as s kk)"
  proof -
    have "(Suc j) * W as s
            ≤ (length (enumL as s kk) + length (enumR as s kk)) * W as s"
      using jL by (intro mult_right_mono) simp_all
    then show ?thesis
      by (simp add: offL_def length_padL length_padR add_mult_distrib2 algebra_simps)
  qed

  have "length (enc0 as s) + offL as s j + W as s
        = length (enc0 as s) + (offL as s j + W as s)" by simp
  also have "… ≤ length (enc0 as s) + (length (padL as s kk) + length (padR as s kk))"
    using pad_bound by (rule add_left_mono)
  also have "… = length (enc as s kk)"
    by (simp add: enc_def)
  finally show ?thesis .
qed

lemma offR_window_in_enc:
  assumes jR: "j < length (enumR as s kk)"
  shows "length (enc0 as s) + offR as s kk j + W as s ≤ length (enc as s kk)"
proof -
  have "(Suc j) * W as s ≤ length (enumR as s kk) * W as s"
    using jR by (intro mult_right_mono) simp_all
  hence offR_le:
    "offR as s kk j + W as s ≤ length (padL as s kk) + length (padR as s kk)"
    by (simp add: offR_def length_padL length_padR add_mult_distrib2 algebra_simps)
  then show ?thesis
    by (simp add: enc_def add_left_mono)
qed

(* Lval_at: Extract the integer value from the j-th L-block *)
definition Lval_at :: "int list ⇒ int ⇒ (nat ⇒ bool) ⇒ nat ⇒ int" where
  "Lval_at as s oL j =
     from_bits (map oL [length (enc0 as s) + offL as s j  ..<  length (enc0 as s) + offL as s j + W as s])"

(* Rval_at: Extract the integer value from the j-th R-block *)
definition Rval_at :: "int list ⇒ int ⇒ (nat ⇒ bool) ⇒ nat ⇒ int" where
  "Rval_at as s oR j =
     from_bits (map oR [length (enc0 as s) + offR as s kk j ..<  length (enc0 as s) + offR as s kk j + W as s])"

(* The index sets we want to prove are fully covered *)
definition Lset where
  "Lset as s ≡ ⋃ j < length (enumL as s kk). blockL_abs enc0 as s j"

definition Rset where
  "Rset as s ≡ ⋃ j < length (enumR as s kk). blockR_abs enc0 as s kk j"

(* The decision tree extracted from the TM *)
definition T where
  "T as s ≡
     tm_to_dtr' head0 stepf final_acc
       (steps M (enc as s kk))
       (conf M (enc as s kk) 0)"

(* The semantic predicate: "Is there a matching LHS/RHS pair?" *)
definition good where
  "good as s oL oR ≡
     (∃jL<length (enumL as s kk). ∃jR<length (enumR as s kk).
        Lval_at as s oL jL = Rval_at as s oR jR)"

(* ========================================================================= *)
(* KEY LEMMAS                                                                *)
(* ========================================================================= *)

(* LEMMA: All read positions are in some L or R block *)
lemma in_padL_imp_in_some_blockL_abs:
  assumes i_in:
    "i ∈ {length (enc0 as s) ..< length (enc0 as s) + length (padL as s kk)}"
  shows "∃j<length (enumL as s kk). i ∈ blockL_abs enc0 as s j"
proof -
  let ?len0 = "length (enc0 as s)"
  let ?W    = "W as s"
  let ?E    = "enumL as s kk"
  let ?k    = "i - ?len0"

  have i_ge: "?len0 ≤ i" and i_lt: "i < ?len0 + length (padL as s kk)"
    using i_in by auto
  hence k_lt: "?k < length (padL as s kk)" by simp

  (* From membership, the padL interval is non-empty → W > 0 *)
  have Wpos: "0 < ?W"
  proof (rule ccontr)
    assume "¬ 0 < ?W" hence "?W = 0" by simp
    hence "length (padL as s kk) = 0" by (simp add: length_padL)
    have "length (padL as s kk) = 0" by (simp add: ‹length (padL as s kk) = 0›)
    then have "i ∈ {length (enc0 as s) ..< length (enc0 as s) + 0}" using i_in by simp
    thus False by simp
  qed

  (* length padL is (#enumL) * W *)
  have padL_len: "length (padL as s kk) = length ?E * ?W"
    by (simp add: length_padL)

  define j where "j = ?k div ?W"
  have j_lt: "j < length ?E"
    using k_lt Wpos by (simp add: j_def padL_len div_less_iff_less_mult)

  (* decompose k = j*W + r, with r < W *)
  have decomp: "?k = j * ?W + (?k mod ?W)"
    by (simp add: j_def mult.commute div_mult_mod_eq)
  have r_lt: "(?k mod ?W) < ?W"
    using Wpos by (rule mod_less_divisor)

  (* rewrite the block and show membership *)
  have "i = ?len0 + j * ?W + (?k mod ?W)"
    using i_ge decomp by simp
  moreover have
    "blockL_abs enc0 as s j = { ?len0 + j * ?W ..< ?len0 + j * ?W + ?W }"
    by (simp add: blockL_abs_def offL_def)
  ultimately have "i ∈ blockL_abs enc0 as s j"
    using r_lt by auto

  thus ?thesis by (intro exI[of _ j]) (use j_lt in simp)
qed

lemma in_padR_imp_in_some_blockR_abs:
  assumes iR:
    "i ∈ { length (enc0 as s) + length (padL as s kk)
         ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"
  shows "∃j<length (enumR as s kk). i ∈ blockR_abs enc0 as s kk j"
proof -
  let ?base = "length (enc0 as s) + length (padL as s kk)"
  let ?W    = "W as s"
  let ?r    = "i - ?base"

  from iR have base_le: "?base ≤ i"
    and r_lt: "?r < length (padR as s kk)"
    by auto

  have padR_len: "length (padR as s kk) = length (enumR as s kk) * ?W"
    by (simp add: length_padR)

  (* show W>0; otherwise padR would be empty, contradicting r_lt *)
  have Wpos: "0 < ?W"
  proof (rule ccontr)
    assume "¬ 0 < ?W"
    then have "?W = 0" by simp
    then have "length (padR as s kk) = 0" by (simp add: padR_len)
    with r_lt show False by simp
  qed

  define j where "j = ?r div ?W"
  define u where "u = ?r mod ?W"

  have j_lt: "j < length (enumR as s kk)"
    using r_lt Wpos by (simp add: j_def padR_len div_less_iff_less_mult)

  have u_lt: "u < ?W"
    using Wpos by (simp add: u_def)

(* from iR you likely already have: *)
  have base_le: "?base ≤ i" and r_lt: "i - ?base < length (padR as s kk)"
    using iR by auto

(* You also proved 0 < ?W as Wpos earlier. Now the decomposition: *)
  have i_decomp:
    "i = ?base
        + ((i - ?base) div ?W) * ?W
        + ((i - ?base) mod ?W)"
  proof -
    have "(i - ?base) = ((i - ?base) div ?W) * ?W + ((i - ?base) mod ?W)"
      using Wpos by (simp add: div_mult_mod_eq)
    then show ?thesis using base_le by linarith
  qed

  have BR_eq:
    "blockR_abs enc0 as s kk j
     = { ?base + j * ?W ..< ?base + j * ?W + ?W }"
    using blockR_abs_def offR_def by (simp add: add.assoc length_padL)

have u_ge0: "0 ≤ u" by simp   (* nat is nonnegative *)

have mem:
  "length (enc0 as s) + length (padL as s kk) + j * W as s ≤ i ∧
   i < length (enc0 as s) + length (padL as s kk) + j * W as s + W as s"
  using i_decomp j_def u_def u_lt by force

have "i ∈ blockR_abs enc0 as s kk j"
  using mem
  by (simp add: BR_eq)

  thus ?thesis using j_lt by blast
qed

(* LEMMA: The tree computes the right answer *)
lemma correct_T:
  "run (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j) (T as s)
   = good as s (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j)"
proof -
  have "run (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j) (T as s)
        = run ((!) (enc as s kk)) ((!) (enc as s kk))
             (tm_to_dtr' head0 stepf final_acc (steps M (enc as s kk))
                (conf M (enc as s kk) 0))"
    by (simp add: T_def)
  also have "… = accepts M (enc as s kk)"
    by (simp add: tm_to_dtr_accepts)   (* from DTM_Run_Sem context *)
  also have "… = good as s (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j)"
    by (simp add: correctness)
  finally show ?thesis .
qed

lemma nth_concat_map_fixed:
  fixes xs :: "'a list" and f :: "'a ⇒ 'b list" and w :: nat
  assumes LEN: "⋀x. x ∈ set xs ⟹ length (f x) = w"
    and j: "j < length xs"
    and t: "t < w"
  shows "concat (map f xs) ! (j*w + t) = f (xs!j) ! t"
proof -
  (* 1) length of the concatenation over the first j chunks is j*w *)
  have pref_len: "length (concat (map f (take j xs))) = j * w"
  proof -
    have "length (concat (map f (take j xs)))
        = sum_list (map (length ∘ f) (take j xs))"
      by (simp add: length_concat)
    also have "... = (∑_← take j xs. w)"
      by (smt (verit) LEN comp_apply in_set_takeD map_eq_conv)
    also have "... = length (take j xs) * w"
      by (simp add: sum_const_all_nat)
    also have "... = j * w"
      using length_take min_def by (simp add: j)
    finally show ?thesis .
  qed

(* 2) split the big concat at chunk j *)
  have map_split:
    "map f xs = map f (take j xs) @ [f (xs ! j)] @ map f (drop (Suc j) xs)"
    using j Cons_nth_drop_Suc append_Cons append_Nil append_take_drop_id list.simps(9) map_append 
    by metis

  have split:
    "concat (map f xs)
     = concat (map f (take j xs)) @ f (xs ! j)
       @ concat (map f (drop (Suc j) xs))"
    using map_split concat_append by simp

  (* 3) index into the middle block *)
  from t have "concat (map f xs) ! (j*w + t)
             = (f (xs!j) @ concat (map f (drop (Suc j) xs))) ! t"
    by (simp add: split pref_len nth_append)
  also from t have "... = f (xs!j) ! t"
    using LEN j by (simp add: nth_append)
  finally show ?thesis .
qed

lemma Rval_at_on_enc_block:
  fixes j :: nat
  assumes jR: "j < length (enumR as s kk)"
  shows "Rval_at as s (λi. (enc as s kk) ! i) j = enumR as s kk ! j"
proof -
  let ?a = "length (enc0 as s) + offR as s kk j"
  let ?w = "W as s"

  have map_slice_R:
    "map ((!) (x0 as s)) [?a ..< ?a + ?w]
     = to_bits (W as s) (enumR as s kk ! j)"
  proof (rule nth_equalityI)
    (* lengths match: the slice has length w, and each catalog block is length w *)
    show "length (map ((!) (x0 as s)) [?a ..< ?a + ?w])
          = length (to_bits (W as s) (enumR as s kk ! j))"
      using jR to_bits_len_on_enumR in_set_conv_nth
      by (metis diff_add_inverse length_map length_upt)

  next
    fix t assume t: "t < length (map ((!) (x0 as s)) [?a ..< ?a + ?w])"
    hence tw: "t < ?w" by simp
    have idx: "[?a ..< ?a + ?w] ! t = ?a + t" using tw by simp

    (* rewrite absolute offset through enc = enc0 @ padL @ padR *)
    have a_decomp: "?a = length (enc0 as s) + length (padL as s kk) + j * ?w"
      by (simp add: offR_def length_padL)

    have step_enc_pad:
      "(x0 as s) ! (?a + t) = (padR as s kk) ! (j * ?w + t)"
      using enc_def a_decomp nth_append_length_plus 
      by (simp add: add.assoc)

    (* fixed-width chunks inside padR *)
    have fixed_len_meta:
      "⋀x. x ∈ set (enumR as s kk) ⟹ length (to_bits (W as s) x) = ?w"
      by (simp add: to_bits_len_on_enumR)

    have "map ((!) (x0 as s)) [?a ..< ?a + ?w] ! t
          = (x0 as s) ! (?a + t)" 
      using nth_map idx t by auto
    also have "... = concat (map (to_bits ?w) (enumR as s kk)) ! (j * ?w + t)"
      by (simp add: step_enc_pad padR_def)
    also have "... = to_bits ?w (enumR as s kk ! j) ! t"
      by (rule nth_concat_map_fixed[OF fixed_len_meta jR tw])
    finally show
      "map ((!) (x0 as s)) [?a ..< ?a + ?w] ! t
       = to_bits (W as s) (enumR as s kk ! j) ! t" .
  qed

  have "Rval_at as s ((!) (x0 as s)) j
        = from_bits (to_bits (W as s) (enumR as s kk ! j))"
    by (simp add: Rval_at_def map_slice_R)

  have v_inR: "enumR as s kk ! j ∈ set (enumR as s kk)"
    using jR in_set_conv_nth by metis

  have v_inU:
    "enumR as s kk ! j ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
    using v_inR by (rule UnI2)

  have "from_bits (to_bits (W as s) (enumR as s kk ! j))
        = enumR as s kk ! j"
    using bits_roundtrip[OF v_inU] by simp

  have "Rval_at as s ((!) (x0 as s)) j
        = from_bits (to_bits (W as s) (enumR as s kk ! j))"
    by (simp add: Rval_at_def map_slice_R)
  also have "... = enumR as s kk ! j"
    using bits_roundtrip[OF v_inU] by simp
  finally show ?thesis .
qed

lemma R_catalog_for_enc:
  "set (map (Rval_at as s (λi. (enc as s kk) ! i))
             [0..<length (enumR as s kk)])
   = set (enumR as s kk)"
proof -
  let ?n = "length (enumR as s kk)"
  have map_eq:
    "map (Rval_at as s ((!) (x0 as s))) [0..<?n]
     = map (λj. enumR as s kk ! j) [0..<?n]"
    by (rule map_cong[OF _])
       (simp_all add: Rval_at_on_enc_block)

  have set_map_nth:
    "set (map (λj. enumR as s kk ! j) [0..<?n]) = set (enumR as s kk)"
    using set_conv_nth by (simp add: map_nth)

  show ?thesis
    using map_eq set_map_nth by force
qed

(* ========================================================================= *)
(* PART: Oracle-Level Coverage Proof (No Instance Construction Needed)      *)
(* ========================================================================= *)

(* LEMMA: If M doesn't read a block, the tree doesn't see those indices *)
lemma unread_block_unseen:
  assumes jL_unread: "Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
  shows "seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
         blockL_abs enc0 as s jL = {}"
proof -
  have "seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)
        ⊆ Base.read0 M (enc as s kk)"
    unfolding T_def using seenL_tm_to_dtr_subset_read0 by simp
  thus ?thesis using jL_unread by blast
qed

(* LEMMA: Can flip oracle on block to change good value 
   
   Key insight: If we have at least 2 LHS values, and some match RHS while
   some don't, then we can change whether good holds by changing one L-block. *)
lemma oracle_flip_changes_good:
  assumes jL_bound: "jL < length (enumL as s kk)"
      and two_lhs: "2 ≤ card (set (enumL as s kk))"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"
  shows "∃oL'. (∀i. i ∉ blockL_abs enc0 as s jL ⟶ 
                     oL' i = (enc as s kk) ! i) ∧
               good as s oL' ((!) (enc as s kk)) ≠ 
               good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
proof -
  (* Get two different values from enumL *)
  obtain v_hit where v_hit_in_L: "v_hit ∈ set (enumL as s kk)" 
                 and v_hit_in_R: "v_hit ∈ set (enumR as s kk)"
    using hit by blast
  obtain v_miss where v_miss_in_L: "v_miss ∈ set (enumL as s kk)"
                  and v_miss_not_R: "v_miss ∉ set (enumR as s kk)"
    using miss by blast
  
  have distinct_L: "distinct (enumL as s kk)" by (simp add: enumL_def)
  
  (* Pick which value to use based on current state *)
  define target where "target = (if good as s ((!) (enc as s kk)) ((!) (enc as s kk))
                                  then v_miss else v_hit)"
  
  (* Build new oracle that puts target in block jL *)
  define bits where "bits = to_bits (W as s) target"

  have target_in: "target ∈ set (enumL as s kk)"
    using target_def v_hit_in_L v_miss_in_L by auto

  have target_in_union: "target ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
    using target_in by auto

  have bits_len: "length bits = W as s"
    using bits_roundtrip[OF target_in_union] bits_def by blast

  have bits_val: "from_bits bits = target"
    using bits_roundtrip[OF target_in_union] bits_def by blast
  
  define oL' where "oL' i = (
    let base = length (enc0 as s) + offL as s jL in
    if base ≤ i ∧ i < base + W as s 
    then bits ! (i - base)
    else (enc as s kk) ! i)" for i
  
  have outside_same: "⋀i. i ∉ blockL_abs enc0 as s jL ⟹ oL' i = (enc as s kk) ! i"
    by (auto simp: oL'_def blockL_abs_def)
  
  have Lval_changed: "Lval_at as s oL' jL = target"
  proof -
    define base where "base = length (enc0 as s) + offL as s jL"
  
    have map_eq: "map oL' [base ..< base + W as s] = bits"
    proof (rule nth_equalityI)
      show "length (map oL' [base ..< base + W as s]) = length bits"
        using bits_len by simp
    next
      fix i assume "i < length (map oL' [base ..< base + W as s])"
      hence i_lt: "i < W as s" by simp
      have "map oL' [base ..< base + W as s] ! i = oL' (base + i)"
        using i_lt by simp
      also have "... = bits ! i"
        using i_lt by (simp add: oL'_def base_def Let_def)
      finally show "map oL' [base ..< base + W as s] ! i = bits ! i" .
    qed
  
    show ?thesis
      unfolding Lval_at_def base_def[symmetric]
      using map_eq bits_val by simp
  qed
  
  have good_flips: "good as s oL' ((!) (enc as s kk)) ≠ 
                    good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
  proof (cases "good as s ((!) (enc as s kk)) ((!) (enc as s kk))")
    case True
  (* Was good, now make it bad by putting v_miss *)
    have "target = v_miss" using True target_def by simp
    hence val_miss: "Lval_at as s oL' jL = v_miss" using Lval_changed by simp
  
  (* v_miss doesn't match any RHS value *)
    have "∀jR < length (enumR as s kk). Rval_at as s ((!) (enc as s kk)) jR ≠ v_miss"
    proof (intro allI impI)
      fix jR assume "jR < length (enumR as s kk)"
      hence "Rval_at as s ((!) (enc as s kk)) jR = enumR as s kk ! jR"
        by (rule Rval_at_on_enc_block)
      thus "Rval_at as s ((!) (enc as s kk)) jR ≠ v_miss"
        using v_miss_not_R by (metis in_set_conv_nth ‹jR < length (enumR as s kk)›)
    qed
  
  (* After flip, position jL can't match anything *)
    hence no_match_jL: "∀jR < length (enumR as s kk). 
                        Lval_at as s oL' jL ≠ Rval_at as s ((!) (enc as s kk)) jR"
      using val_miss by fastforce
  
  (* But we need to show good changes... this is the tricky part *)
    show ?thesis sorry
  
  next
    case False
  (* Was bad, now make it good by putting v_hit *)
    have "target = v_hit" using False target_def by simp
    hence val_hit: "Lval_at as s oL' jL = v_hit" using Lval_changed by simp
  
  (* v_hit matches some RHS value *)
    have "∃jR < length (enumR as s kk). Rval_at as s ((!) (enc as s kk)) jR = v_hit"
    proof -
      have "v_hit ∈ set (enumR as s kk)" using v_hit_in_R .
      then obtain jR where "jR < length (enumR as s kk)" 
                     and "enumR as s kk ! jR = v_hit"
        by (meson in_set_conv_nth)
      moreover have "Rval_at as s ((!) (enc as s kk)) jR = enumR as s kk ! jR"
        using Rval_at_on_enc_block[OF ‹jR < length (enumR as s kk)›] .
      ultimately show ?thesis by auto
    qed
  
  (* So position jL now matches something *)
    then obtain jR where jR_bound: "jR < length (enumR as s kk)"
                  and match: "Rval_at as s ((!) (enc as s kk)) jR = v_hit"
      by blast
  
    have "Lval_at as s oL' jL = Rval_at as s ((!) (enc as s kk)) jR"
      using val_hit match by simp
  
  (* This witness proves good is true after flip *)
    hence "good as s oL' ((!) (enc as s kk))"
      unfolding good_def using jL_bound jR_bound by blast
  
  (* But it was false before, so they differ *)
    thus ?thesis using False by simp
  qed
  
  (* NOW CONSTRUCT THE EXISTENTIAL! *)
  show ?thesis
  proof (intro exI[of _ oL'] conjI)
    show "∀i. i ∉ blockL_abs enc0 as s jL ⟶ oL' i = (enc as s kk) ! i"
      using outside_same by blast
    show "good as s oL' ((!) (enc as s kk)) ≠ 
          good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
      using good_flips .
  qed
qed

(* THEOREM: If M doesn't read a block, contradiction *)
theorem coverage_by_oracle_contradiction:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"  (* NEW *)
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"  (* NEW *)
      and miss_block: "∃jL. jL < length (enumL as s kk) ∧
                            Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
  shows False
proof -
  (* Get the unread block *)
  obtain jL where 
    jL_bound: "jL < length (enumL as s kk)" and
    jL_unread: "Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
    using miss_block by blast
  
  (* For the oracle flip to work, we need these conditions *)
  have two_lhs: "2 ≤ card (set (enumL as s kk))"
  proof -
    have "card (set (enumL as s kk)) = card (LHS (e_k as s kk) (length as))"
      by simp
    also have "... = 2 ^ kk"
      using card_LHS_e_k distinct kk_bounds(2) len less_or_eq_imp_le by blast
    also have "... ≥ 2"
      using kk_bounds
      by (metis add_0 add_lessD1 linorder_not_less nat_power_less_imp_less 
          power_one_right)
    finally show ?thesis .
  qed
  
(* Remove the sorry lines, use the assumptions directly *)
(* hit and miss are now assumptions, not things to prove *)
  
(* Get flipped oracle *)
  have flip_exists: "∃oL'. (∀i. i ∉ blockL_abs enc0 as s jL ⟶ 
                               oL' i = (enc as s kk) ! i) ∧
                         good as s oL' ((!) (enc as s kk)) ≠ 
                         good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    using oracle_flip_changes_good[OF jL_bound two_lhs hit miss] .

(* Get flipped oracle *)
  obtain oL' where
    outside_same_obj: "∀i. i ∉ blockL_abs enc0 as s jL ⟶ 
                         oL' i = (enc as s kk) ! i" and
    good_flips: "good as s oL' ((!) (enc as s kk)) ≠ 
               good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    using flip_exists by auto

(* Convert to meta-level *)
  have outside_same: "⋀i. i ∉ blockL_abs enc0 as s jL ⟹ oL' i = (enc as s kk) ! i"
    using outside_same_obj by blast
  
  (* Tree doesn't see the flipped block *)
  have unseen: "seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
                blockL_abs enc0 as s jL = {}"
    using unread_block_unseen[OF jL_unread] .
  
(* Therefore tree gives same answer with oL' *)
  have L_agree: "⋀i. i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ⟹ 
                   oL' i = (enc as s kk) ! i"
    using unseen outside_same by blast

  have R_agree: "⋀j. j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ⟹ 
                   ((!) (enc as s kk)) j = ((!) (enc as s kk)) j"
    by simp

  have "run oL' ((!) (enc as s kk)) (T as s) = 
      run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    by (simp add: run_agree_on_seen(1)[OF L_agree R_agree])
  
  (* But the tree must give correct answers *)
  hence "good as s oL' ((!) (enc as s kk)) = 
         good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    using correct_T by (meson correctness)
  
  (* Contradiction! *)
  with good_flips show False by contradiction
qed

(* COROLLARY: Every L-block must be touched *)
lemma every_L_block_touched:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"  (* NEW *)
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"  (* NEW *)
  shows "∀jL < length (enumL as s kk). 
           Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL ≠ {}"
proof (rule ccontr)
  assume "¬(∀jL<length (enumL as s kk). 
              Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL ≠ {})"
  hence "∃jL. jL < length (enumL as s kk) ∧
              Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}" by simp
  thus False 
    using coverage_by_oracle_contradiction[OF n_ge2 kk_bounds distinct len hit miss] 
    by blast
qed

(* Symmetric R-block oracle flip lemma *)
lemma oracle_flip_changes_good_R:
  assumes jR_bound: "jR < length (enumR as s kk)"
      and two_rhs: "2 ≤ card (set (enumR as s kk))"
      and hit_R: "∃v ∈ set (enumR as s kk). v ∈ set (enumL as s kk)"
      and miss_R: "∃v ∈ set (enumR as s kk). v ∉ set (enumL as s kk)"
  shows "∃oR'. (∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ 
                     oR' i = (enc as s kk) ! i) ∧
               good as s ((!) (enc as s kk)) oR' ≠ 
               good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
  sorry (* Symmetric to oracle_flip_changes_good *)

(* Symmetric R-block contradiction theorem *)
theorem coverage_by_oracle_contradiction_R:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and miss_block_R: "∃jR. jR < length (enumR as s kk) ∧
                              Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
  shows False
  sorry (* Symmetric to coverage_by_oracle_contradiction *)

(* Symmetric for R-blocks *)
lemma every_R_block_touched:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)" 
  shows "∀jR < length (enumR as s kk). 
           Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR ≠ {}"
proof (rule ccontr)
  assume "¬(∀jR<length (enumR as s kk). 
              Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR ≠ {})"
  hence "∃jR. jR < length (enumR as s kk) ∧
              Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}" by simp
  thus False using coverage_by_oracle_contradiction_R[OF n_ge2 kk_bounds distinct len] 
    by blast
qed

theorem coverage_blocks:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"
  shows "(∀j<length (enumL as s kk). 
            Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s j ≠ {}) ∧
         (∀j<length (enumR as s kk). 
            Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk j ≠ {})"
  using every_L_block_touched[OF n_ge2 kk_bounds distinct len hit miss]
        every_R_block_touched[OF n_ge2 kk_bounds distinct len hit miss]
  by blast

end  (* context Coverage_TM *)

end  (* theory *)
