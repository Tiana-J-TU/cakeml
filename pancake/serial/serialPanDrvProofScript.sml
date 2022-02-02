open preamble backendTheory panLangTheory word_to_wordTheory pan_to_wordTheory;
open serialPanDrvTheory panSemTheory;

val _ = new_theory "serialPanDrvProof"

Definition uart_device_oracle_def:
  uart_device_oracle = ARB (* TODO (eventually) *)
End

Definition uart_init_state_def:
  uart_init_state ck be mem memaddrs ffi base_addr =
  <| locals := FEMPTY;
     code := FEMPTY |++ serialProg;
     eshapes := FEMPTY; (* TODO: should there be something here? *)
     memory := mem;
     memaddrs := memaddrs;
     clock := ck;
     be := be;
     ffi := ffi;
     base_addr := base_addr;
    |>
End

val _ = Datatype ‘
  reg32=
  <| byte1 : word8 ;
     byte2 : word8 ;
     byte3 : word8 ;
     byte4 : word8 ;
   |>’

(* :'ffi *)
val _ = Datatype ‘
  uart_ffi=
  <| utrstat : reg32 llist ;
     rxbuf   : reg32 llist ;
   |>’

Definition init_uart_ffi:
  init_uart_ffi= <| utrstat := [||]; rxbuf := [||] |>
End              
(* val _ = Datatype ‘
  uart_ffi=
  <| utrstat : word32 llist ;
     rxbuf   : word32 llist ;
   |>’
*)
   
Definition uart_ffi_oracle:
  (uart_ffi_oracle :uart_ffi oracle) port st conf bytes=
  case port of
    "write_reg_UTXH" => (if LENGTH conf >= 0 then Oracle_return st bytes
                           (* Modify to update io_event list. *)
                         else Oracle_final FFI_failed)                             
  | "read_reg_UTRSTAT" => (
      if LENGTH bytes >= 4 then
        case st.utrstat of
          [||] => Oracle_final FFI_failed
        | hd:::tl =>
            Oracle_return (st with utrstat := tl)
              [hd.byte1; hd.byte2; hd.byte3; hd.byte4]
      else Oracle_final FFI_failed)      
  | "read_reg_URXH" => (
      if LENGTH bytes >= 4 then
        case st.rxbuf of
          [||] => Oracle_final FFI_failed
        | hd:::tl =>                             
                Oracle_return (st with rxbuf := tl)
                  [hd.byte1; hd.byte2; hd.byte3; hd.byte4]
      else Oracle_final FFI_failed)                      
  | _ => Oracle_final FFI_failed
End
   
Definition uart_ffi_state:
  uart_ffi_state=
  <| oracle := uart_ffi_oracle;
     ffi_state := init_uart_ffi;
     io_events := [];
   |> :uart_ffi ffi_state 
End

Theorem uart_drv_getcharFun_ready_read:        
(*        
Theorem uart_drv_getcharFun_no_break:
  ∀ck be mem memaddrs ffi res s.
    (evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi) = (res,s)) ∧
    preconditions (* TODO *) ⇒
    res ≠ SOME Break
Proof
  
  cheat
  (* TODO *)
QED
*)

Theorem uart_drv_getcharFun_no_break:
  ∀ck be mem memaddrs ffi base_addr res s.
    preconditions ⇒
    case
      evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
                  uart_init_state ck be mem memaddrs ffi base_addr)
    of
      (SOME Break, s') => F
    | _ => T                  
Proof
  rpt strip_tac >>
  simp [Once evaluate_def,uart_init_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp [eval_def, flookup_fupdate_list, FLOOKUP_UPDATE, OPT_MMAP_def, lookup_code_def] >>
  IF_CASES_TAC >- simp[] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp [Once evaluate_def] >>
  simp [eval_def, dec_clock_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp [Once evaluate_def] >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def] >>
  qmatch_goalsub_abbrev_tac ‘a3 (evaluate _)’ >>
  simp [Once evaluate_def] >>
  simp[eval_def, FLOOKUP_UPDATE] >>
  simp [Once evaluate_def] >>
  simp[eval_def, FLOOKUP_UPDATE] >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a4 (a5 (a6 (evaluate _)))’ >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  simp [Once evaluate_def] >>
  simp[FLOOKUP_UPDATE] >>
  Cases_on ‘read_bytearray base_addr 8 (mem_load_byte mem' memaddrs be)’
  >- (simp [] >> unabbrev_all_tac >> simp []) >>
  simp [] >>
  Cases_on ‘read_bytearray (base_addr + 64w) 32 (mem_load_byte mem' memaddrs be)’
  >- (simp [] >> unabbrev_all_tac >> simp []) >>
  simp [] >>
  Cases_on ‘call_FFI ffi "read_reg_UTRSTAT" x x'’ 
  >- (simp [] >> unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp[Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
     simp[Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def] >>
     Cases_on ‘mem_stores (base_addr + 128w) (flatten (ValWord 0w)) memaddrs
                 (write_bytearray (base_addr + 64w) l mem' memaddrs be)’
     >- (simp [] >> unabbrev_all_tac >> simp []) >>
     simp [] >> unabbrev_all_tac >> simp[] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
     simp [Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_store_byte x'' memaddrs be (base_addr + 160w) (w2w (base_addr + 64w))’
     >- (simp [] >> unabbrev_all_tac >> simp []) >>
     simp [] >> unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
     simp [Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_store_byte x'³' memaddrs be (base_addr + 168w) (w2w (base_addr + 72w))’
     >- (simp [] >> unabbrev_all_tac >> simp []) >>
     unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
     simp [Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_store_byte x'⁴' memaddrs be (base_addr + 176w) (w2w (base_addr + 80w))’
     >- (unabbrev_all_tac >> simp []) >>
     unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
     simp [Once evaluate_def] >>
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_store_byte x'⁵' memaddrs be (base_addr + 184w) (w2w (base_addr + 88w))’
     >- (unabbrev_all_tac >> simp []) >>             
     unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>
     unabbrev_all_tac >> simp [] >>
     qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
     simp [Once evaluate_def] >>     
     simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
     Cases_on ‘mem_load One (base_addr + 128w) memaddrs x'⁶'’
     >- (unabbrev_all_tac >> simp []) >>
     simp [wordLangTheory.word_op_def, wordLangTheory.word_sh_def] >>
     IF_CASES_TAC
     >- (simp[] >>
         IF_CASES_TAC 
         >- (simp [evaluate_def, FLOOKUP_UPDATE] >>
             Cases_on ‘read_bytearray base_addr 8 (mem_load_byte x'⁶' memaddrs be)’
             >- (unabbrev_all_tac >> simp []) >>
             unabbrev_all_tac >> simp [] >>
             Cases_on ‘read_bytearray (base_addr + 64w) 32 (mem_load_byte x'⁶' memaddrs be)’
             >- simp [] >> simp [] >>
             Cases_on ‘call_FFI f "read_reg_URXH" x'⁸' x'⁹'’
             >- (simp [] >>
                 simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE] >>
                 Cases_on ‘mem_load_byte (write_bytearray (base_addr + 64w) l' x'⁶' memaddrs be)
                             memaddrs be (base_addr + 64w)’
                 >- simp [] >>
                 simp [] >>
                 simp [size_of_shape_def, shape_of_def]) >>
             simp []) >>
         simp [Once evaluate_def] >>
         simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE,
               size_of_shape_def, shape_of_def] >>
         unabbrev_all_tac >> simp []) >>
     unabbrev_all_tac >> simp []) >>
     unabbrev_all_tac >> simp []
QED

(*
simp[Once evaluate_def]         
simp [eval_def]
simp [eval_def, wordLangTheory.word_op_def]
simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, FLOOKUP_UPDATE]
simp [OPT_MMAP_def]
simp [wordLangTheory.word_op_def]
simp [eval_def, OPTION_BIND_def]
simp[eval_def, FLOOKUP_UPDATE] >>
simp [OPTION_MAP_DEF]
simp [fcpTheory.dimindex_def, wordLangTheory.word_sh_def]
*)

Theorem uart_drv_getcharFun_no_error:
  ∀ck be mem memaddrs ffi base_addr res s.
   read_bytearray base_addr 8 (mem_load_byte mem memaddrs be) = SOME x ∧
   read_bytearray (base_addr + 64w) 32 (mem_load_byte mem memaddrs be) = SOME x' ∧
   (∀f l. call_FFI ffi "read_reg_UTRSTAT" x x' = FFI_return f l ⇒
     (mem_stores (base_addr + 128w) (flatten (ValWord 0w)) memaddrs
               (write_bytearray (base_addr + 64w) l mem memaddrs be) = SOME x'' ∧
     mem_store_byte x'' memaddrs be (base_addr + 160w)
          (w2w (base_addr + 64w)) = SOME x''' ∧
     mem_store_byte x''' memaddrs be (base_addr + 168w) (w2w (base_addr + 72w)) = SOME x'''' ∧
     mem_store_byte x'⁴' memaddrs be (base_addr + 176w) (w2w (base_addr + 80w)) = SOME x''''' ∧
     mem_store_byte x'⁵' memaddrs be (base_addr + 184w) (w2w (base_addr + 88w)) = SOME x'''''' ∧
     mem_load One (base_addr + 128w) memaddrs x'⁶' = SOME x'⁷' ∧ x'⁷' = ValWord v ∧
     read_bytearray base_addr 8 (mem_load_byte x'⁶' memaddrs be) = SOME y ∧
     read_bytearray (base_addr + 64w) 32 (mem_load_byte x'⁶' memaddrs be) = SOME y' ∧
     (∀ f' l'. call_FFI f "read_reg_URXH" y y' = FFI_return f' l'
                ⇒ (mem_load_byte (write_bytearray (base_addr + 64w) l' x'⁶' memaddrs be)
       memaddrs be (base_addr + 64w) = SOME y''))))

    ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi base_addr) of
      (SOME Error,s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  IF_CASES_TAC >- simp[] >>
  simp[Once evaluate_def] >>
  simp[Once eval_def] >> simp[dec_clock_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp[Once evaluate_def] >>
  simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a3 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a4 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a5 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
  simp[Once evaluate_def,FLOOKUP_UPDATE] >>
  Cases_on ‘call_FFI ffi "read_reg_UTRSTAT" x x'’
  >- (last_x_assum $ qspecl_then [`f`, `l`] assume_tac >> 
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp [Once evaluate_def] >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
      simp [Once evaluate_def] >>      
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
      simp [FLOOKUP_UPDATE] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>      
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp [Once evaluate_def] >>      
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def, FLOOKUP_UPDATE, OPTION_BIND_def] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>      
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp [Once evaluate_def] >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def, FLOOKUP_UPDATE, OPTION_BIND_def] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>      
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp [Once evaluate_def] >>      
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def, FLOOKUP_UPDATE, OPTION_BIND_def] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>      
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (evaluate _))))’ >>
      simp [Once evaluate_def] >>
      simp [eval_def, OPT_MMAP_def] >>
      simp [wordLangTheory.word_op_def, OPTION_MAP_DEF] >>
      simp [fcpTheory.dimindex_def, wordLangTheory.word_sh_def] >>
      Cases_on ‘1w && v ≠ 0w’
      >- (simp [] >>
          simp [Once evaluate_def] >>
          qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
          simp [Once evaluate_def] >>
          simp[eval_def, FLOOKUP_UPDATE] >>
          Cases_on ‘call_FFI f "read_reg_URXH" y y'’ 
          >- (unabbrev_all_tac >> simp [] >>
              qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (evaluate _))))’ >>
              simp [Once evaluate_def] >>
              simp[eval_def, FLOOKUP_UPDATE] >>
              simp [size_of_shape_def, shape_of_def] >>
              unabbrev_all_tac >> simp []) >>
              Cases_on ‘FFI_final f'’
              >- (simp [] >>
              unabbrev_all_tac >> simp [] >>
              qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (evaluate _))))’ >>
              simp [Once evaluate_def] >>
              simp[eval_def, FLOOKUP_UPDATE] >>
              simp [size_of_shape_def, shape_of_def] >>
              unabbrev_all_tac >> simp []) >>
         simp [] >> unabbrev_all_tac >> simp []) >>
      simp [Once evaluate_def] >>
      simp[eval_def, FLOOKUP_UPDATE] >>
      simp [size_of_shape_def, shape_of_def] >>
      unabbrev_all_tac >> simp []) >>
  simp[] >> unabbrev_all_tac >> simp []
QED

(* qpat_x_assum ‘_ ⇒ _’ mp_tac >> simp[] *)             
        
Theorem uart_drv_getcharFun_no_error:
  ∀ck be mem memaddrs ffi base_addr res s.
    IS_SOME(read_bytearray base_addr 8 (mem_load_byte mem memaddrs be)) ∧
    IS_SOME(read_bytearray (base_addr + 64w) 32 (mem_load_byte mem memaddrs be)) ∧
    IS_SOME(mem_stores (base_addr + 128w) (flatten (ValWord 0w)) memaddrs
             (write_bytearray (base_addr + 64w) l mem memaddrs be)) ∧
    more preconditions (* TODO *) ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi base_addr) of
      (SOME Error,s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  IF_CASES_TAC >- simp[] >>
  simp[dec_clock_def] >>
  simp[Once evaluate_def] >>
  simp[Once eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp[Once evaluate_def] >>
  simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a3 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a4 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a5 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
  simp[Once evaluate_def,FLOOKUP_UPDATE] >>
  Cases_on ‘read_bytearray base_addr 8 (mem_load_byte mem' memaddrs be)’
  >- (simp[] >>
      unabbrev_all_tac >>
      fs[]) >>
  simp[] >>
  Cases_on ‘read_bytearray (base_addr + 64w) 32 (mem_load_byte mem' memaddrs be)’
  >- fs [] >> simp[] >>
  Cases_on ‘call_FFI ffi "read_reg_UTRSTAT" x x'’
  >- (simp [] >>
      unabbrev_all_tac >> simp [] >>
      qmatch_goalsub_abbrev_tac ‘a1 (a2 (a3 (a4 (a5 (evaluate _)))))’ >>
      simp [Once evaluate_def] >>
      qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
      simp[Once evaluate_def] >>
      simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
      Cases_on ‘mem_stores (base_addr + 128w) (flatten (ValWord 0w)) memaddrs
        (write_bytearray (base_addr + 64w) l' mem' memaddrs be)’
      >- (simp [] >> unabbrev_all_tac >> simp []
                
  cheat (* TODO *)
QED

(*        
Theorem uart_drv_getcharFun_no_error:
  ∀ck be mem memaddrs ffi res s.
    (evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi) = (res,s)) ∧
    preconditions (* TODO *) ⇒
    res ≠ SOME Error
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  simp[Once eval_def]
  (* TODO *)
QED
*)

(* Arbitrarily set ck to be at least 3 for exploration purposes. *)        
Theorem uart_drv_putcharFun_timeout_cond:
  ∀ck be mem memaddrs ffi base_addr res s c.
    ck >= 3 ⇒
    case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const $ n2w c],
                  uart_init_state ck be mem memaddrs ffi base_addr)
    of
      (SOME TimeOut, s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  simp [eval_def, OPTION_BIND_def, shape_of_def] >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp[Once evaluate_def] >>
  simp[eval_def,dec_clock_def, flookup_fupdate_list] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def, OPT_MMAP_def,wordLangTheory.word_op_def] >>
  simp[flookup_fupdate_list, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac ‘a3 (a4 (evaluate _))’ >>
  simp[Once evaluate_def,eval_def] >>
  simp[flookup_fupdate_list, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac ‘a5 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a8 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a10 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def, dec_clock_def, flookup_fupdate_list, FLOOKUP_UPDATE] >>
  Cases_on ‘read_bytearray base_addr 8 (mem_load_byte mem' memaddrs be)’ 
  >- (unabbrev_all_tac >> simp []) >>
  unabbrev_all_tac >> simp [flookup_fupdate_list, FLOOKUP_UPDATE] >>

  cheat 
QED

Theorem uart_drv_getcharFun_no_break:
  ∀ck be mem memaddrs ffi base_addr res s c.
    preconditions ⇒
    case
      evaluate (Call Tail (Label (strlit "uart_drv_putchar")) [Const $ n2w c],
                  uart_init_state ck be mem memaddrs ffi base_addr)
    of
      (SOME Break, s') => F
    | _ => T                  
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  simp [eval_def, OPTION_BIND_def, shape_of_def] >>
  simp [Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp[Once evaluate_def] >>
  simp[eval_def,dec_clock_def, flookup_fupdate_list] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def, OPT_MMAP_def,wordLangTheory.word_op_def] >>
  simp[flookup_fupdate_list, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac ‘a3 (a4 (evaluate _))’ >>
  simp[Once evaluate_def,eval_def] >>
  simp[flookup_fupdate_list, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac ‘a5 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  Induct_on ‘ck’ >- (simp []) >>
  simp[flookup_fupdate_list, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a7 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  Cases_on ‘ck’ >- (unabbrev_all_tac >> simp []) >>
  simp [] >>
  qmatch_goalsub_abbrev_tac ‘a8 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a9 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a10 (evaluate _)’ >>
  simp[eval_def,dec_clock_def, flookup_fupdate_list, FLOOKUP_UPDATE] >>
  Cases_on ‘read_bytearray base_addr 8 (mem_load_byte mem' memaddrs be)’
  >- (unabbrev_all_tac >> simp []) >>
  simp [Abbr ‘a10’] >>
  Cases_on ‘read_bytearray (base_addr + 64w) 32 (mem_load_byte mem' memaddrs be)’
  >- unabbrev_all_tac >> simp [] >>
  simp [] >> fs [flookup_fupdate_list, FLOOKUP_UPDATE] >>
  Cases_on ‘call_FFI ffi "read_reg_UTRSTAT" x x'’ 
  >> cheat  
QED


                  
QED  

Theorem uart_drv_getcharFun_no_FinalFFI:
  ∀ck be mem memaddrs ffi base_addr.
    (∀x x'. case call_FFI ffi "read_reg_UTRSTAT" x x' of
                FFI_final _ => F
              | FFI_return f _ =>
                  (∀f' x x'. call_FFI f "read_reg_URXH" x x' ≠ FFI_final f')) ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi base_addr) of
      (SOME (FinalFFI _),s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
       uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,
       lookup_code_def] >>
  IF_CASES_TAC >- simp[] >>
  simp[dec_clock_def] >>
  simp[Once evaluate_def] >>
  simp[Once eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp[Once evaluate_def] >>
  simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a3 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a4 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a5 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
  simp[Once evaluate_def,FLOOKUP_UPDATE] >>
  CASE_TAC
  >- (CASE_TAC >> unabbrev_all_tac >> fs[])
  >> CASE_TAC >-(unabbrev_all_tac >> fs[]) >>
  fs[] >> CASE_TAC
  >- (simp[]>>unabbrev_all_tac >> fs[]>>
      fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
         wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
         OPT_MMAP_def, eval_def, evaluate_def]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]>>
      qpat_abbrev_tac ‘case_term = mem_load One (_ + _) _ _’>>
      Cases_on ‘case_term’>>fs[]>>
      CASE_TAC>>fs[]>>
      CASE_TAC>>fs[]>>
      IF_CASES_TAC>>fs[]>>
      fs[evaluate_def,eval_def,FLOOKUP_UPDATE]>>
      CASE_TAC>>fs[]>>
      CASE_TAC>>fs[]>>
      CASE_TAC>>fs[FLOOKUP_UPDATE]
      >-(CASE_TAC>>fs[shape_of_def, size_of_shape_def])>>
      rename1 ‘call_FFI _ _ x' x = FFI_return f l’>>
      first_assum(qspecl_then [‘x'’, ‘x’] assume_tac)>>
      FULL_CASE_TAC>>fs[]>>
      simp[Once evaluate_def]>>fs[eval_def, FLOOKUP_UPDATE]>>
      simp[shape_of_def, size_of_shape_def])>>
  unabbrev_all_tac >> gs[]>>
  rename1 ‘call_FFI _ _ x' x = FFI_final _’>>
  first_assum(qspecl_then [‘x'’, ‘x’] assume_tac)>> FULL_CASE_TAC>>gs[]
QED

Theorem uart_drv_getcharFun_no_None:
  ∀ck be mem memaddrs ffi base_addr res s.
    IS_SOME(read_bytearray base_addr 8 (mem_load_byte mem memaddrs be)) ∧
    IS_SOME(read_bytearray (base_addr + 64w) 32
                           (mem_load_byte mem memaddrs be)) ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi base_addr) of
      (NONE : 64 result option,s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
       uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,
       OPT_MMAP_def,lookup_code_def] >>
  IF_CASES_TAC >- fs[] >>
  simp[dec_clock_def] >>
  simp[evaluate_def, eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
       FLOOKUP_UPDATE] >>
  CASE_TAC >> fs[] >>
  CASE_TAC >> fs[] >>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  fs[OPTION_MAP_DEF, OPTION_BIND_def, wordLangTheory.word_sh_def]>>
  qpat_abbrev_tac ‘case_term = mem_load One (_ + _) _ _’>>
  Cases_on ‘case_term’ >>fs[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  IF_CASES_TAC>>fs[evaluate_def,eval_def,FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[FLOOKUP_UPDATE]>>
  CASE_TAC>>fs[shape_of_def, size_of_shape_def]>>
  fs[evaluate_def,eval_def,shape_of_def, size_of_shape_def]
QED

val _ = export_theory();
