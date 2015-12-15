open preamble stackLangTheory labLangTheory;
local open stack_removeTheory stack_namesTheory in (* stack-to-stack transformations *) end

val _ = new_theory "stack_to_lab";

val max_lab_def = Define `
  max_lab (p:'a stackLang$prog) =
    case p of
    | Seq p1 p2 => MAX (max_lab p1) (max_lab p2)
    | If _ _ _ p1 p2 => MAX (max_lab p1) (max_lab p2)
    | Call NONE _ NONE => 0
    | Call NONE _ (SOME (_,_,l2)) => l2
    | Call (SOME (_,_,_,l2)) _ NONE => l2
    | Call (SOME (_,_,_,l2)) _ (SOME (_,_,l3)) => MAX l2 l3
    | _ => 0`

val no_ret_def = Define `
  no_ret (p:'a stackLang$prog) =
    case p of
    | Halt _ => T
    | Raise _ => T
    | Return _ _ => T
    | Seq p1 p2 => no_ret p1 \/ no_ret p2
    | If _ _ _ p1 p2 => no_ret p1 /\ no_ret p2
    | Call NONE _ _ => T
    | Call (SOME (p1,_,_,_)) _ NONE => no_ret p1
    | Call (SOME (p1,_,_,_)) _ (SOME (p2,_,_)) => no_ret p1 /\ no_ret p2
    | _ => F`

val compile_jump_def = Define `
  (compile_jump (INL n) = LabAsm (Jump (Lab n 0)) 0w [] 0) /\
  (compile_jump (INR r) = Asm (JumpReg r) [] 0)`;

val negate_def = Define `
  (negate Less = NotLess) /\
  (negate Equal = NotEqual) /\
  (negate Lower = NotLower) /\
  (negate Test = NotTest) /\
  (negate NotLess = Less) /\
  (negate NotEqual = Equal) /\
  (negate NotLower = Lower) /\
  (negate NotTest = Test)`

val _ = export_rewrites ["negate_def"];

val flatten_def = Define `
  flatten p n m =
    case p of
    | Tick => ([Asm (Inst (Skip)) [] 0],m)
    | Inst a => ([Asm (Inst a) [] 0],m)
    | Halt _ => ([LabAsm Halt 0w [] 0],m)
    | Seq p1 p2 =>
        let (xs,m) = flatten p1 n m in
        let (ys,m) = flatten p2 n m in
          (xs ++ ys, m)
    | If c r ri p1 p2 =>
        let (xs,m) = flatten p1 n m in
        let (ys,m) = flatten p2 n m in
          if (p1 = Skip) /\ (p2 = Skip) then ([],m)
          else if p1 = Skip then
            ([LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             [Label n m 0],m+1)
          else if p2 = Skip then
            ([LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0] ++ xs ++
             [Label n m 0],m+1)
          else if no_ret p1 then
            ([LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0] ++ xs ++
             [Label n m 0] ++ ys,m+1)
          else if no_ret p2 then
            ([LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             [Label n m 0] ++ xs,m+1)
          else
            ([LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++
             [LabAsm (Jump (Lab n (m+1))) 0w [] 0; Label n m 0] ++ xs ++
             [Label n (m+1) 0],m+2)
    | Raise r => ([Asm (JumpReg r) [] 0],m)
    | Return r _ => ([Asm (JumpReg r) [] 0],m)
    | Call NONE dest _ => ([compile_jump dest],m)
    | Call (SOME (p1,lr,l1,l2)) dest handler =>
        let (xs,m) = flatten p1 n m in
          ([LabAsm (LocValue lr (Lab l1 l2)) 0w [] 0;
            compile_jump dest; Label l1 l2 0] ++ xs ++
           (case handler of
            | NONE => []
            | SOME (p2,k1,k2) =>
                let (ys,m) = flatten p2 n m in
                  [LabAsm (Jump (Lab n m)) 0w [] 0;
                   Label k1 k2 0] ++ ys ++ [Label n m 0]),
           if IS_SOME handler then m+1 else m)
    | JumpLess r1 r2 target =>
        ([LabAsm (JumpCmp Less r1 (Reg r2) (Lab target 0)) 0w [] 0],m)
    | FFI ffi_index _ _ lr => ([LabAsm (LocValue lr (Lab n m)) 0w [] 0;
                                LabAsm (CallFFI ffi_index) 0w [] 0;
                                Label n m 0],m+1)
    | _  => ([],m)`

val prog_to_section_def = Define `
  prog_to_section (n,p) = Section n (FST (flatten p n (max_lab p)))`

val move_inst_def = Define `
  move_inst dest src =
    if dest = src then Skip else
      Seq (Inst (Const dest 0w))
          (Inst (Arith (Binop Or dest dest (Reg src))))`

val sub_inst_def = Define `
  sub_inst r1 r2 =
    Inst (Arith (Binop Sub r1 r1 (Reg r2)))`

val const_inst_def = Define `
  const_inst r1 w =
    Inst (Const r1 w)`

val seq_list_def = Define `
  (seq_list [] = Skip) /\
  (seq_list [x] = x) /\
  (seq_list (x::xs) = Seq x (seq_list xs))`

val stub0_def = Define `
  stub0 sp bp =
    (0:num, seq_list [move_inst bp 3; (* init base pointer *)
                      move_inst sp 4; (* init stack pointer *)
                      move_inst 0 sp;
                      sub_inst 0 bp;
                      const_inst 4 (word_offset store_length);
                      sub_inst 3 4;
                      (* stack length in 0,
                         first program point in 1,
                         heap start is in 2,
                         heap end is in 3 *)
                      Call NONE (INL 1) NONE])`;

val stub1_def = Define `
  stub1 (start:num) =
    (1:num, seq_list [Set Handler 0;
                      Set ProgStart 1;
                      Set CurrHeap 2;
                      Set EndOfHeap 3;
                      Call NONE (INL start) NONE])`

val _ = Datatype`config =
  <| reg_names : num num_map
   ; stack_ptr : num
   ; base_ptr : num
   |>`;

val compile_def = Define `
  compile start c prog =
    let prog' = stub1 start :: prog in
    let without_stack = stub0 c.stack_ptr c.base_ptr :: stack_remove$compile c.stack_ptr prog' in
    let with_target_names = stack_names$compile c.reg_names without_stack in
    MAP prog_to_section with_target_names`;

val _ = export_theory();
