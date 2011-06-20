(* ------------------------------------------------------------------------- *)
(* Memory safety for the H interface.                                        *)
(* ------------------------------------------------------------------------- *)

logfile "h-def";;

(* Physical pages *)

new_type_abbrev("region_length",`:num`);;

new_type_abbrev("reference_count",`:num`);;

new_type_abbrev("superpage_address",`:word10`);;

new_type_abbrev("superpage_offset",`:word10`);;

new_type_abbrev("offset",`:word12`);;

new_type_abbrev("physical_page_address",
                `:superpage_address # superpage_offset`);;

new_type_abbrev("physical_address",`:physical_page_address # offset`);;

let physical_page_address_lt_def = new_definition
  `!pdi1 pti1 pdi2 pti2.
     physical_page_address_lt (pdi1,pti1) (pdi2,pti2) <=>
     word10_lt pdi1 pdi2 \/ (pdi1 = pdi2 /\ word10_lt pti1 pti2)`;;

export_thm physical_page_address_lt_def;;

let physical_page_address_le_def = new_definition
  `!vpa1 vpa2.
     physical_page_address_le vpa1 vpa2 <=>
     ~physical_page_address_lt vpa2 vpa1`;;

export_thm physical_page_address_le_def;;

let physical_page_address_inc_raw_def = new_definition
  `!pdi pti.
     physical_page_address_inc (pdi,pti) =
     if pti = num_to_word10 1023 then
       (word10_add pdi (num_to_word10 1), num_to_word10 0)
     else
       (pdi, word10_add pti (num_to_word10 1))`;;

let physical_page_address_inc_def = prove
  (`!pdi pti.
      (word10_lt pti (num_to_word10 1023) ==>
       physical_page_address_inc (pdi,pti) =
       (pdi, word10_add pti (num_to_word10 1))) /\
      (word10_lt pdi (num_to_word10 1023) ==>
       physical_page_address_inc (pdi, num_to_word10 1023) =
       (word10_add pdi (num_to_word10 1), num_to_word10 0))`,
   REWRITE_TAC [physical_page_address_inc_raw_def] THEN
   REPEAT GEN_TAC THEN
   bool_cases_tac `pti = num_to_word10 1023` THENL
   [ASM_REWRITE_TAC [word10_lt_refl];
    ASM_REWRITE_TAC []]);;

export_thm physical_page_address_inc_def;;

let physical_page_address_add_def = new_recursive_definition num_RECURSION
  `(!ppa. physical_page_address_add ppa 0 = ppa) /\
   (!ppa n.
      physical_page_address_add ppa (SUC n) =
      physical_page_address_add (physical_page_address_inc ppa) n)`;;

export_thm physical_page_address_add_def;;

(* Page contents *)

new_type_abbrev("page_data",`:offset -> byte`);;

let zero_page_data_def = new_definition
  `!off. zero_page_data (off : offset) = num_to_byte 0`;;

export_thm zero_page_data_def;;

let update_page_data_def = new_definition
  `!off v f off'.
      update_page_data (off : offset) (v : byte) (f : page_data) off' =
      if off = off' then v else f off'`;;

export_thm update_page_data_def;;

(* Page directories *)

new_type_abbrev("page_directory",`:physical_page_address`);;

new_type_abbrev("page_directory_index",`:superpage_address`);;

let directory_contents_induct,directory_contents_recursion = define_type
    "directory_contents =
       Superpage superpage_address
     | Table physical_page_address";;

export_thm directory_contents_induct;;
export_thm directory_contents_recursion;;

let case_directory_contents_def =
  new_recursive_definition directory_contents_recursion
  `(!s t spa. case_directory_contents s t (Superpage spa) = (s spa : A)) /\
   (!s t ppa. case_directory_contents s t (Table ppa) = (t ppa : A))`;;

export_thm case_directory_contents_def;;

new_type_abbrev("directory_page_data",
                `:page_directory_index -> directory_contents option`);;

(* Page tables *)

new_type_abbrev("page_table_index",`:superpage_offset`);;

new_type_abbrev("table_page_data",
                `:page_table_index -> physical_page_address option`);;

(* Virtual addresses *)

new_type_abbrev("virtual_page_address",
                `:page_directory_index # page_table_index`);;

new_type_abbrev("virtual_address",`:virtual_page_address # offset`);;

let virtual_page_address_lt_def = new_definition
  `!pdi1 pti1 pdi2 pti2.
     virtual_page_address_lt (pdi1,pti1) (pdi2,pti2) <=>
     word10_lt pdi1 pdi2 \/ (pdi1 = pdi2 /\ word10_lt pti1 pti2)`;;

export_thm virtual_page_address_lt_def;;

let virtual_page_address_le_def = new_definition
  `!vpa1 vpa2.
     virtual_page_address_le vpa1 vpa2 <=>
     ~virtual_page_address_lt vpa2 vpa1`;;

export_thm virtual_page_address_le_def;;

let virtual_page_address_inc_raw_def = new_definition
  `!pdi pti.
     virtual_page_address_inc (pdi,pti) =
     if pti = num_to_word10 1023 then
       (word10_add pdi (num_to_word10 1), num_to_word10 0)
     else
       (pdi, word10_add pti (num_to_word10 1))`;;

let virtual_page_address_inc_def = prove
  (`!pdi pti.
      (word10_lt pti (num_to_word10 1023) ==>
       virtual_page_address_inc (pdi,pti) =
       (pdi, word10_add pti (num_to_word10 1))) /\
      (word10_lt pdi (num_to_word10 1023) ==>
       virtual_page_address_inc (pdi, num_to_word10 1023) =
       (word10_add pdi (num_to_word10 1), num_to_word10 0))`,
   REWRITE_TAC [virtual_page_address_inc_raw_def] THEN
   REPEAT GEN_TAC THEN
   bool_cases_tac `pti = num_to_word10 1023` THENL
   [ASM_REWRITE_TAC [word10_lt_refl];
    ASM_REWRITE_TAC []]);;

export_thm virtual_page_address_inc_def;;

let virtual_page_address_add_def = new_recursive_definition num_RECURSION
  `(!ppa. virtual_page_address_add ppa 0 = ppa) /\
   (!ppa n.
      virtual_page_address_add ppa (SUC n) =
      virtual_page_address_add (virtual_page_address_inc ppa) n)`;;

export_thm virtual_page_address_add_def;;

let user_kernel_boundary_def = new_definition
  `user_kernel_boundary = (num_to_word10 768, num_to_word10 0)`;;

export_thm user_kernel_boundary_def;;

let is_user_page_address_def = new_definition
  `!vpa.
     is_user_page_address vpa =
     virtual_page_address_lt vpa user_kernel_boundary`;;

export_thm is_user_page_address_def;;

let is_kernel_page_address_def = new_definition
  `!vpa.
     is_kernel_page_address vpa <=> ~is_user_page_address vpa`;;

export_thm is_kernel_page_address_def;;

let is_user_address_def = new_definition
  `!vpa off.
     is_user_address ((vpa,off) : virtual_address) =
     is_user_page_address vpa`;;

export_thm is_user_address_def;;

let is_kernel_address_def = new_definition
  `!vpa off.
     is_kernel_address ((vpa,off) : virtual_address) =
     is_kernel_page_address vpa`;;

export_thm is_kernel_address_def;;

(* Page types *)

let page_induct,page_recursion = define_type
    "page =
       Environment page_data
     | Normal page_data
     | PageDirectory directory_page_data
     | PageTable table_page_data
     | NotInstalled";;

export_thm page_induct;;
export_thm page_recursion;;

let dest_environment_def = new_recursive_definition page_recursion
  `(!pd. dest_environment (Environment pd) = SOME pd) /\
   (!pd. dest_environment (Normal pd) = NONE) /\
   (!pd. dest_environment (PageDirectory pd) = NONE) /\
   (!pd. dest_environment (PageTable pd) = NONE) /\
   (dest_environment NotInstalled = NONE)`;;

export_thm dest_environment_def;;

let dest_normal_def = new_recursive_definition page_recursion
  `(!pd. dest_normal (Environment pd) = NONE) /\
   (!pd. dest_normal (Normal pd) = SOME pd) /\
   (!pd. dest_normal (PageDirectory pd) = NONE) /\
   (!pd. dest_normal (PageTable pd) = NONE) /\
   (dest_normal NotInstalled = NONE)`;;

export_thm dest_normal_def;;

let dest_environment_or_normal_def = new_recursive_definition page_recursion
  `(!pd. dest_environment_or_normal (Environment pd) = SOME pd) /\
   (!pd. dest_environment_or_normal (Normal pd) = SOME pd) /\
   (!pd. dest_environment_or_normal (PageDirectory pd) = NONE) /\
   (!pd. dest_environment_or_normal (PageTable pd) = NONE) /\
   (dest_environment_or_normal NotInstalled = NONE)`;;

export_thm dest_environment_or_normal_def;;

let dest_page_directory_def = new_recursive_definition page_recursion
  `(!pd. dest_page_directory (Environment pd) = NONE) /\
   (!pd. dest_page_directory (Normal pd) = NONE) /\
   (!pd. dest_page_directory (PageDirectory pd) = SOME pd) /\
   (!pd. dest_page_directory (PageTable pd) = NONE) /\
   (dest_page_directory NotInstalled = NONE)`;;

export_thm dest_page_directory_def;;

let dest_page_table_def = new_recursive_definition page_recursion
  `(!pd. dest_page_table (Environment pd) = NONE) /\
   (!pd. dest_page_table (Normal pd) = NONE) /\
   (!pd. dest_page_table (PageDirectory pd) = NONE) /\
   (!pd. dest_page_table (PageTable pd) = SOME pd) /\
   (dest_page_table NotInstalled = NONE)`;;

export_thm dest_page_table_def;;

let is_not_installed_def = new_recursive_definition page_recursion
  `(!pd. is_not_installed (Environment pd) = F) /\
   (!pd. is_not_installed (Normal pd) = F) /\
   (!pd. is_not_installed (PageDirectory pd) = F) /\
   (!pd. is_not_installed (PageTable pd) = F) /\
   (is_not_installed NotInstalled = T)`;;

export_thm is_not_installed_def;;

let is_environment_def = new_definition
  `!p. is_environment p <=> is_some (dest_environment p)`;;

export_thm is_environment_def;;

let is_normal_def = new_definition
  `!p. is_normal p <=> is_some (dest_normal p)`;;

export_thm is_normal_def;;

let is_page_directory_def = new_definition
  `!p. is_page_directory p <=> is_some (dest_page_directory p)`;;

export_thm is_page_directory_def;;

let is_page_table_def = new_definition
  `!p. is_page_table p <=> is_some (dest_page_table p)`;;

export_thm is_page_table_def;;

let is_page_directory_or_table_def = new_definition
  `!p.
     is_page_directory_or_table p <=>
     is_page_directory p \/ is_page_table p`;;

export_thm is_page_directory_or_table_def;;

let is_installed_def = new_definition
  `!p. is_installed p <=> ~is_not_installed p`;;

export_thm is_installed_def;;

(* Regions of physical memory *)

let physical_region_induct,physical_region_recursion = define_type
    "physical_region =
       PhysicalRegion
         physical_page_address
         region_length";;

export_thm physical_region_induct;;
export_thm physical_region_recursion;;

let physical_region_start_def =
  new_recursive_definition physical_region_recursion
  `!s l. physical_region_start (PhysicalRegion s l) = s`;;

export_thm physical_region_start_def;;

let physical_region_length_def =
  new_recursive_definition physical_region_recursion
  `!s l. physical_region_length (PhysicalRegion s l) = l`;;

export_thm physical_region_length_def;;

let physical_region_to_list_def =
  new_recursive_definition physical_region_recursion
  `!s l.
     physical_region_to_list (PhysicalRegion s l) =
     MAP (physical_page_address_add s) (interval 0 l)`;;

export_thm physical_region_to_list_def;;

let forall_physical_region_def = new_definition
  `!p pr.
     forall_physical_region p pr <=>
     ALL p (physical_region_to_list pr)`;;

export_thm forall_physical_region_def;;

let exists_physical_region_def = new_definition
  `!p pr.
     exists_physical_region p pr <=>
     EX p (physical_region_to_list pr)`;;

export_thm exists_physical_region_def;;

let member_physical_region_def = new_definition
  `!ppa pr.
     member_physical_region ppa pr <=>
     MEM ppa (physical_region_to_list pr)`;;

export_thm member_physical_region_def;;

let is_physical_subregion_def = new_definition
  `!pr1 pr2.
     is_physical_subregion pr1 pr2 <=>
     forall_physical_region (\ppa. member_physical_region ppa pr2) pr1`;;

export_thm is_physical_subregion_def;;

(* Regions of virtual memory *)

let virtual_region_induct,virtual_region_recursion = define_type
    "virtual_region =
       VirtualRegion
         virtual_page_address
         region_length";;

export_thm virtual_region_induct;;
export_thm virtual_region_recursion;;

let virtual_region_start_def =
  new_recursive_definition virtual_region_recursion
  `!s l. virtual_region_start (VirtualRegion s l) = s`;;

export_thm virtual_region_start_def;;

let virtual_region_length_def =
  new_recursive_definition virtual_region_recursion
  `!s l. virtual_region_length (VirtualRegion s l) = l`;;

export_thm virtual_region_length_def;;

let virtual_region_to_list_def =
  new_recursive_definition virtual_region_recursion
  `!s l.
     virtual_region_to_list (VirtualRegion s l) =
     MAP (virtual_page_address_add s) (interval 0 l)`;;

export_thm virtual_region_to_list_def;;

let forall_virtual_region_def = new_definition
  `!p vr.
     forall_virtual_region p vr <=>
     ALL p (virtual_region_to_list vr)`;;

export_thm forall_virtual_region_def;;

let exists_virtual_region_def = new_definition
  `!p vr.
     exists_virtual_region p vr <=>
     EX p (virtual_region_to_list vr)`;;

export_thm exists_virtual_region_def;;

let member_virtual_region_def = new_definition
  `!ppa vr.
     member_virtual_region ppa vr <=>
     MEM ppa (virtual_region_to_list vr)`;;

export_thm member_virtual_region_def;;

let is_virtual_subregion_def = new_definition
  `!vr1 vr2.
     is_virtual_subregion vr1 vr2 <=>
     forall_virtual_region (\ppa. member_virtual_region ppa vr2) vr1`;;

export_thm is_virtual_subregion_def;;

let is_user_region_def = new_definition
  `!vr.
     is_user_region vr <=>
     forall_virtual_region is_user_page_address vr`;;

export_thm is_user_region_def;;

let is_kernel_region_def = new_definition
  `!vr.
     is_kernel_region vr <=>
     forall_virtual_region is_kernel_page_address vr`;;

export_thm is_kernel_region_def;;

(* The state of the machine *)

let region_state_induct,region_state_recursion = define_type
    "region_state =
       RegionState
         (physical_region set)
         (physical_region set)";;

export_thm region_state_induct;;
export_thm region_state_recursion;;

let initial_regions_def = new_recursive_definition region_state_recursion
  `!i a. initial_regions (RegionState i a) = i`;;

export_thm initial_regions_def;;

let all_regions_def = new_recursive_definition region_state_recursion
  `!i a. all_regions (RegionState i a) = a`;;

export_thm all_regions_def;;

let state_induct,state_recursion = define_type
    "state =
       State
         page_directory
         page_directory
         (physical_page_address -> page)
         region_state";;

export_thm state_induct;;
export_thm state_recursion;;

let cr3_def = new_recursive_definition state_recursion
  `!c r s g. cr3 (State c r s g) = c`;;

export_thm cr3_def;;

let reference_def = new_recursive_definition state_recursion
  `!c r s g. reference (State c r s g) = r`;;

export_thm reference_def;;

let status_def = new_recursive_definition state_recursion
  `!c r s g. status (State c r s g) = s`;;

export_thm status_def;;

let regions_def = new_recursive_definition state_recursion
  `!c r s g. regions (State c r s g) = g`;;

export_thm regions_def;;

let translate_page_def = new_definition
  `!s pd pdi pti.
     translate_page s pd (pdi,pti) =
     case_option
       NONE
       (\pdd.
          case_option
            NONE
            (case_directory_contents
               (\spa. SOME (spa,pti))
               (\ppa.
                  case_option
                    NONE
                    (\tpd. tpd pti)
                    (dest_page_table (status s ppa))))
            (pdd pdi))
       (dest_page_directory (status s pd))`;;

export_thm translate_page_def;;

let translation_def = new_definition
  `!s vpa (off : offset).
     translation s (vpa,off) =
     case_option
       NONE
       (\ppa. SOME (ppa,off))
       (translate_page s (cr3 s) vpa)`;;

export_thm translation_def;;

let reference_count_def = new_definition
  `!s pd ppa.
     reference_count s pd ppa =
     CARD { vpa | translate_page s pd vpa = SOME ppa }`;;

export_thm reference_count_def;;

let table_mapped_in_directory_def = new_definition
  `!s pd pt.
     table_mapped_in_directory s pd pt <=>
     case_option
       F
       (\pdd. ?pdi. pdd pdi = SOME (Table pt))
       (dest_page_directory (status s pd))`;;

export_thm table_mapped_in_directory_def;;

let mapped_page_def = new_definition
  `!s pd vpa.
     mapped_page s pd vpa <=>
     is_some (translate_page s pd vpa)`;;

export_thm mapped_page_def;;

let unmapped_page_def = new_definition
  `!s ppa.
     unmapped_page s ppa <=>
     !pd.
       is_page_directory (status s pd) ==>
       !vpa. ~(translate_page s pd vpa = SOME ppa)`;;

export_thm unmapped_page_def;;

let is_normal_page_def = new_definition
  `!s ppa. is_normal_page s ppa <=> is_normal (status s ppa)`;;

export_thm is_normal_page_def;;

let unmapped_normal_page_def = new_definition
  `!s ppa.
     unmapped_normal_page s ppa <=>
     unmapped_page s ppa /\ is_normal_page s ppa`;;

export_thm unmapped_normal_page_def;;

(* Protection domains *)

let domain_induct,domain_recursion = define_type
    "domain =
       EDomain
     | HDomain
     | KDomain
     | UDomain";;

export_thm domain_induct;;
export_thm domain_recursion;;

let action_induct,action_recursion = define_type
    "action =
       WriteE virtual_address byte
     | DeriveRegionH physical_region physical_page_address region_length
     | AllocatePageDirectoryH physical_page_address
     | FreePageDirectoryH page_directory
     | AddMappingH
         page_directory (physical_page_address list)
         physical_region virtual_region
     | RemoveMappingH page_directory virtual_region
     | AddKernelMappingH physical_region virtual_region
     | ExecuteH page_directory
     | WriteK virtual_address byte
     | WriteU virtual_address byte";;

export_thm action_induct;;
export_thm action_recursion;;

let domain_def = new_recursive_definition action_recursion
  `(!va b. domain (WriteE va b) = EDomain) /\
   (!pr ppa l. domain (DeriveRegionH pr ppa l) = HDomain) /\
   (!ppa. domain (AllocatePageDirectoryH ppa) = HDomain) /\
   (!pd. domain (FreePageDirectoryH pd) = HDomain) /\
   (!pd ppas pr vr. domain (AddMappingH pd ppas pr vr) = HDomain) /\
   (!pd vr. domain (RemoveMappingH pd vr) = HDomain) /\
   (!pr vr. domain (AddKernelMappingH pr vr) = HDomain) /\
   (!pd. domain (ExecuteH pd) = HDomain) /\
   (!va b. domain (WriteK va b) = KDomain) /\
   (!va b. domain (WriteU va b) = UDomain)`;;

export_thm domain_def;;

let e_view_induct,e_view_recursion = define_type
    "e_view =
       EView
         (virtual_page_address -> (page_data # reference_count) option)";;

export_thm e_view_induct;;
export_thm e_view_recursion;;

let e_observable_pages_def = new_recursive_definition e_view_recursion
  `!f. e_observable_pages (EView f) = f`;;

export_thm e_observable_pages_def;;

let view_e_def = new_definition
  `!s.
     view_e s =
     EView
       (\vpa.
          case_option
            NONE
            (\ppa.
               case_option
                 NONE
                 (\f. SOME (f, reference_count s (cr3 s) ppa))
                 (dest_environment (status s ppa)))
            (translate_page s (cr3 s) vpa))`;;

export_thm view_e_def;;

let h_view_induct,h_view_recursion = define_type
    "h_view =
       HView
         page_directory
         (physical_page_address -> page option)
         region_state
         page_directory";;

export_thm h_view_induct;;
export_thm h_view_recursion;;

let current_pdir_def = new_recursive_definition h_view_recursion
  `!c p g r. current_pdir (HView c p g r) = c`;;

export_thm current_pdir_def;;

let pages_def = new_recursive_definition h_view_recursion
  `!c p g r. pages (HView c p g r) = p`;;

export_thm pages_def;;

let h_region_handles_def = new_recursive_definition h_view_recursion
  `!c p g r. h_region_handles (HView c p g r) = g`;;

export_thm h_region_handles_def;;

let reference_pdir_def = new_recursive_definition h_view_recursion
  `!c p g r. reference_pdir (HView c p g r) = r`;;

export_thm reference_pdir_def;;

let view_h_def = new_definition
  `!s.
     view_h s =
     HView
       (cr3 s)
       (\ppa.
          let page = status s ppa in
          if is_normal page then NONE else SOME page)
       (regions s)
       (reference s)`;;

export_thm view_h_def;;

let k_view_induct,k_view_recursion = define_type
    "k_view =
       KView
         (virtual_page_address -> (page_data # reference_count) option)
         region_state";;

export_thm k_view_induct;;
export_thm k_view_recursion;;

let k_observable_pages_def = new_recursive_definition k_view_recursion
  `!f g. k_observable_pages (KView f g) = f`;;

export_thm k_observable_pages_def;;

let k_region_handles_def = new_recursive_definition k_view_recursion
  `!f g. k_region_handles (KView f g) = g`;;

export_thm k_region_handles_def;;

let view_k_def = new_definition
  `!s.
     view_k s =
     KView
       (\vpa.
          case_option
            NONE
            (\ppa.
               case_option
                 NONE
                 (\f. SOME (f, reference_count s (cr3 s) ppa))
                 (if is_kernel_page_address vpa then
                    dest_environment_or_normal (status s ppa)
                  else
                    dest_environment (status s ppa)))
            (translate_page s (cr3 s) vpa))
       (regions s)`;;

export_thm view_k_def;;

let u_view_induct,u_view_recursion = define_type
    "u_view =
       UView
         (virtual_page_address -> (page_data # reference_count) option)";;

export_thm u_view_induct;;
export_thm u_view_recursion;;

let u_observable_pages_def = new_recursive_definition u_view_recursion
  `!f. u_observable_pages (UView f) = f`;;

export_thm u_observable_pages_def;;

let view_u_def = new_definition
  `!s.
     view_u s =
     UView
       (\vpa.
          if is_user_page_address vpa then
            case_option
              NONE
              (\ppa.
                 case_option
                   NONE
                   (\f. SOME (f, reference_count s (cr3 s) ppa))
                   (dest_normal (status s ppa)))
              (translate_page s (cr3 s) vpa)
          else
            NONE)`;;

export_thm view_u_def;;

let view_induct,view_recursion = define_type
    "view =
       ViewE e_view
     | ViewH h_view
     | ViewK k_view
     | ViewU u_view";;

export_thm view_induct;;
export_thm view_recursion;;

let view_def = new_recursive_definition domain_recursion
  `(!s. view EDomain s = ViewE (view_e s)) /\
   (!s. view HDomain s = ViewH (view_h s)) /\
   (!s. view KDomain s = ViewK (view_k s)) /\
   (!s. view UDomain s = ViewU (view_u s))`;;

export_thm view_def;;

let view_equiv_def = new_definition
  `!d s t. view_equiv d s t <=> view d s = view d t`;;

export_thm view_equiv_def;;

(* Output *)

new_type_abbrev("output",`:view`);;

(* Well-formedness conditions *)

let cr3_is_page_directory_def = new_definition
  `!s.
     cr3_is_page_directory s <=>
     is_page_directory (status s (cr3 s))`;;

export_thm cr3_is_page_directory_def;;

let reference_is_page_directory_def = new_definition
  `!s.
     reference_is_page_directory s <=>
     is_page_directory (status s (reference s))`;;

export_thm reference_is_page_directory_def;;

let reference_maps_kernel_addresses_def = new_definition
  `!s.
     reference_maps_kernel_addresses s <=>
     !vpa.
       mapped_page s (reference s) vpa ==>
       is_kernel_page_address vpa`;;

export_thm reference_maps_kernel_addresses_def;;

let reference_contains_environment_def = new_definition
  `!s.
     reference_contains_environment s <=>
     !ppa.
       is_environment (status s ppa) ==>
       ?vpa. translate_page s (reference s) vpa = SOME ppa`;;

export_thm reference_contains_environment_def;;

let environment_only_in_reference_def = new_definition
  `!s.
     environment_only_in_reference s <=>
     !pd vpa.
       case_option
         T
         (\ppa.
            is_environment (status s ppa) ==>
            mapped_page s (reference s) vpa)
         (translate_page s pd vpa)`;;

export_thm environment_only_in_reference_def;;

let page_directories_contain_reference_def = new_definition
  `!s.
     page_directories_contain_reference s <=>
     !pd vpa.
       is_page_directory (status s pd) /\
       is_kernel_page_address vpa ==>
       translate_page s pd vpa = translate_page s (reference s) vpa`;;

export_thm page_directories_contain_reference_def;;

let mapped_pages_are_available_def = new_definition
  `!s.
     mapped_pages_are_available s <=>
     !pd vpa.
        case_option
          T
          (\ppa. is_installed (status s ppa))
          (translate_page s pd vpa)`;;

export_thm mapped_pages_are_available_def;;

let table_pointers_are_page_tables_def = new_definition
  `!s.
     table_pointers_are_page_tables s <=>
     !pd pdi.
       case_option
         T
         (\pdd.
            case_option
              T
              (case_directory_contents
                 (\spa. T)
                 (\ppa. is_page_table (status s ppa)))
              (pdd pdi))
         (dest_page_directory (status s pd))`;;

export_thm table_pointers_are_page_tables_def;;

let initial_regions_are_regions_def = new_definition
  `!s.
     initial_regions_are_regions s <=>
     initial_regions (regions s) SUBSET all_regions (regions s)`;;

export_thm initial_regions_are_regions_def;;

let regions_are_not_environment_def = new_definition
  `!s.
     regions_are_not_environment s <=>
     !r ppa.
       r IN all_regions (regions s) /\
       member_physical_region ppa r ==>
       ~is_environment (status s ppa)`;;

export_thm regions_are_not_environment_def;;

(* Need extra condition that all regions are subregions of initial regions? *)
(* Need extra condition that all regions are nonempty? *)

let wellformed_def = new_definition
  `!s.
     wellformed s <=>
     cr3_is_page_directory s /\
     page_directories_contain_reference s /\
     mapped_pages_are_available s /\
     table_pointers_are_page_tables s /\
     reference_is_page_directory s /\
     reference_maps_kernel_addresses s /\
     environment_only_in_reference s /\
     initial_regions_are_regions s /\
     regions_are_not_environment s`;;

export_thm wellformed_def;;

(* Operations in the model *)

let write_e_def = new_definition
  `!va b s s'.
     write_e va b s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     case_option
       F
       (\ (ppa,off).
         !ppa'.
           if ppa' = ppa then
             case_option
               F
               (\f.
                  dest_environment (status s' ppa') =
                  SOME (update_page_data off b f))
               (dest_environment (status s ppa'))
           else
             status s ppa' = status s' ppa')
       (translation s va)`;;

export_thm write_e_def;;

let derive_region_h_def = new_definition
  `!pr ppa l s s'.
     derive_region_h pr ppa l s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     status s = status s' /\
     initial_regions (regions s) = initial_regions (regions s') /\
     let r = PhysicalRegion ppa l in
     is_physical_subregion r pr /\
     ~(r IN all_regions (regions s)) /\
     all_regions (regions s') = r INSERT all_regions (regions s)`;;

export_thm derive_region_h_def;;

let allocate_page_directory_h_def = new_definition
  `!ppa s s'.
     allocate_page_directory_h ppa s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     unmapped_normal_page s ppa /\
     !ppa'.
       status s' ppa' =
       status s (if ppa' = ppa then reference s else ppa)`;;

export_thm allocate_page_directory_h_def;;

let free_page_directory_h_def = new_definition
  `!pd s s'.
     free_page_directory_h pd s s' <=>
     allocate_page_directory_h pd s' s /\
     status s' pd = Normal zero_page_data`;;

export_thm free_page_directory_h_def;;

let add_mapping_def = new_definition
  `!pd pts pr vr s s'.
     add_mapping pd pts pr vr s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     is_page_directory (status s pd) /\
     (!pt. pt IN pts ==> unmapped_normal_page s pt) /\
     (!pt. pt IN pts ==> ~member_physical_region pt pr) /\
     forall_physical_region (is_normal_page s) pr /\
     physical_region_length pr = virtual_region_length vr /\
     is_user_region vr /\
     (!vpa.
        if member_virtual_region vpa vr then
          is_none (translate_page s pd vpa)
        else
          translate_page s' pd vpa = translate_page s pd vpa) /\
     ALL I (zipwith (\vpa ppa. translate_page s' pd vpa = SOME ppa)
              (virtual_region_to_list vr) (physical_region_to_list pr)) /\
     !ppa.
       if ppa IN pts then
         table_mapped_in_directory s' pd ppa
       else if ppa = pd then
         is_page_directory (status s' ppa)
       else if table_mapped_in_directory s pd ppa then
         is_page_table (status s' ppa)
       else
         status s ppa = status s' ppa`;;

let add_mapping_h_def = new_definition
  `!pd pts pr vr s s'.
     add_mapping_h pd pts pr vr s s' <=>
     LENGTH (nub pts) = LENGTH pts /\
     pr IN all_regions (regions s) /\
     ?n.
       n <= LENGTH pts /\
       add_mapping pd (set_of_list (take n pts)) pr vr s s'`;;

export_thm add_mapping_h_def;;

let remove_mapping_h_def = new_definition
  `!pd vr s s'.
     remove_mapping_h pd vr s s' <=>
     case_option
       F
       (\prs.
          let pr = PhysicalRegion prs (virtual_region_length vr) in
          let pts = { ppa | is_page_table (status s ppa) /\
                            status s' ppa = Normal zero_page_data } in
          add_mapping pd pts pr vr s' s)
       (translate_page s pd (virtual_region_start vr))`;;

export_thm remove_mapping_h_def;;

(* Need extra condition that no user data is messed with? *)

let add_kernel_mapping_h_def = new_definition
  `!pr vr s s'.
     add_kernel_mapping_h pr vr s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     pr IN all_regions (regions s) /\
     forall_physical_region (is_normal_page s) pr /\
     physical_region_length pr = virtual_region_length vr /\
     is_kernel_region vr /\
     (!vpa.
        ~member_virtual_region vpa vr ==>
        translate_page s' (reference s') vpa =
        translate_page s (reference s) vpa) /\
     ALL I (zipwith (\vpa ppa. translate_page s' (reference s') vpa = SOME ppa)
              (virtual_region_to_list vr) (physical_region_to_list pr))`;;

export_thm add_kernel_mapping_h_def;;

let execute_h_def = new_definition
  `!pd s s'.
     execute_h pd s s' <=>
     reference s = reference s' /\
     status s = status s' /\
     regions s = regions s' /\
     cr3 s' = pd`;;

export_thm execute_h_def;;

let write_k_def = new_definition
  `!va b s s'.
     write_k va b s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     is_kernel_address va /\
     case_option
       F
       (\ (ppa,off).
          !ppa'.
            if ppa' = ppa then
              case_option
                F
                (\f.
                   dest_normal (status s' ppa') =
                   SOME (update_page_data off b f))
                (dest_normal (status s ppa'))
            else
              status s ppa' = status s' ppa')
       (translation s va)`;;

export_thm write_k_def;;

let write_u_def = new_definition
  `!va b s s'.
     write_u va b s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     is_user_address va /\
     case_option
       F
       (\ (ppa,off).
          !ppa'.
            if ppa' = ppa then
              case_option
                F
                (\f.
                   dest_normal (status s' ppa') =
                   SOME (update_page_data off b f))
                (dest_normal (status s ppa'))
            else
              status s ppa' = status s' ppa')
       (translation s va)`;;

export_thm write_u_def;;

let action_spec_def = new_recursive_definition action_recursion
  `(!va b.
      action_spec (WriteE va b) =
      write_e va b) /\
   (!pr ppa l.
      action_spec (DeriveRegionH pr ppa l) =
      derive_region_h pr ppa l) /\
   (!ppa.
      action_spec (AllocatePageDirectoryH ppa) =
      allocate_page_directory_h ppa) /\
   (!pd.
      action_spec (FreePageDirectoryH pd) =
      free_page_directory_h pd) /\
   (!pd ppas pr vr.
      action_spec (AddMappingH pd ppas pr vr) =
      add_mapping_h pd ppas pr vr) /\
   (!pd vr.
      action_spec (RemoveMappingH pd vr) =
      remove_mapping_h pd vr) /\
   (!pr vr.
      action_spec (AddKernelMappingH pr vr) =
      add_kernel_mapping_h pr vr) /\
   (!pd.
      action_spec (ExecuteH pd) =
      execute_h pd) /\
   (!va b.
      action_spec (WriteK va b) =
      write_k va b) /\
   (!va b.
      action_spec (WriteU va b) =
      write_u va b)`;;

export_thm action_spec_def;;

let action_def = new_definition
  `!a s s'.
      action a s s' <=> wellformed s /\ wellformed s' /\ action_spec a s s'`;;

export_thm action_def;;

(* Security policy *)

let interferes_def = new_definition
  `interferes x y <=>
   (x = EDomain /\ y = EDomain) \/
   (x = EDomain /\ y = HDomain) \/
   (x = EDomain /\ y = KDomain) \/
   (x = HDomain /\ y = HDomain) \/
   (x = HDomain /\ y = KDomain) \/
   (x = HDomain /\ y = UDomain) \/
   (x = KDomain /\ y = KDomain) \/
   (x = KDomain /\ y = UDomain) \/
   (x = UDomain /\ y = KDomain) \/
   (x = UDomain /\ y = UDomain)`;;

export_thm interferes_def;;

logfile "h-thm";;

(* Physical pages *)

(* Page contents *)

(* Page directories *)

let directory_contents_cases = prove_cases_thm directory_contents_induct;;

export_thm directory_contents_cases;;

let directory_contents_distinct = distinctness "directory_contents";;

export_thm directory_contents_distinct;;

let directory_contents_inj = injectivity "directory_contents";;

export_thm directory_contents_inj;;

(* Page tables *)

(* Pages *)

let page_cases = prove_cases_thm page_induct;;

export_thm page_cases;;

let page_distinct = distinctness "page";;

export_thm page_distinct;;

let page_inj = injectivity "page";;

export_thm page_inj;;

(* Regions of physical memory *)

let physical_region_cases = prove_cases_thm physical_region_induct;;

export_thm physical_region_cases;;

let physical_region_inj = injectivity "physical_region";;

export_thm physical_region_inj;;

(* Regions of virtual memory *)

let virtual_region_cases = prove_cases_thm virtual_region_induct;;

export_thm virtual_region_cases;;

let virtual_region_inj = injectivity "virtual_region";;

export_thm virtual_region_inj;;

(* The state of the machine *)

let region_state_cases = prove_cases_thm region_state_induct;;

export_thm region_state_cases;;

let region_state_inj = injectivity "region_state";;

export_thm region_state_inj;;

let state_cases = prove_cases_thm state_induct;;

export_thm state_cases;;

let state_inj = injectivity "state";;

export_thm state_inj;;

(* Protection domains *)

let domain_cases = prove_cases_thm domain_induct;;

export_thm domain_cases;;

let domain_distinct = distinctness "domain";;

export_thm domain_distinct;;

let action_cases = prove_cases_thm action_induct;;

export_thm action_cases;;

let action_distinct = distinctness "action";;

export_thm action_distinct;;

let action_inj = injectivity "action";;

export_thm action_inj;;

let e_view_cases = prove_cases_thm e_view_induct;;

export_thm e_view_cases;;

let e_view_inj = injectivity "e_view";;

export_thm e_view_inj;;

let h_view_cases = prove_cases_thm h_view_induct;;

export_thm h_view_cases;;

let h_view_inj = injectivity "h_view";;

export_thm h_view_inj;;

let k_view_cases = prove_cases_thm k_view_induct;;

export_thm k_view_cases;;

let k_view_inj = injectivity "k_view";;

export_thm k_view_inj;;

let u_view_cases = prove_cases_thm u_view_induct;;

export_thm u_view_cases;;

let u_view_inj = injectivity "u_view";;

export_thm u_view_inj;;

let view_cases = prove_cases_thm view_induct;;

export_thm view_cases;;

let view_distinct = distinctness "view";;

export_thm view_distinct;;

let view_inj = injectivity "view";;

export_thm view_inj;;

let user_page_address_not_kernel = prove
  (`!vpa. is_user_page_address vpa <=> ~is_kernel_page_address vpa`,
   REWRITE_TAC [is_kernel_page_address_def]);;

export_thm user_page_address_not_kernel;;

let translate_page_eq = prove
  (`!s s'.
      (!pd pdi pti.
         translate_page s pd (pdi,pti) =
         translate_page s' pd (pdi,pti)) ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (ISPEC `x' : virtual_page_address` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm translate_page_eq;;

let translate_page_is_page_directory = prove
  (`!s pd vpa.
      is_some (translate_page s pd vpa) ==>
      is_page_directory (status s pd)`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `vpa : virtual_page_address` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [translate_page_def] THEN
   MP_TAC (SPEC `status s pd` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_page_directory_def; is_page_directory_def; is_some_def;
      case_option_def]);;

export_thm translate_page_is_page_directory;;

let translate_page_inj = prove
  (`!s s'.
      (!ppa.
         is_page_directory_or_table (status s ppa) \/
         is_page_directory_or_table (status s' ppa) ==>
         status s ppa = status s' ppa) ==>
      translate_page s = translate_page s'`,
   REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (ISPEC `x' : virtual_page_address` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [translate_page_def] THEN
   POP_ASSUM
     (fun th ->
        MP_TAC (SPEC `x : physical_page_address` th) THEN
        ASSUME_TAC th) THEN
   REWRITE_TAC [is_page_directory_or_table_def; is_page_directory_def] THEN
   MP_TAC (SPEC `status s x` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' x` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_page_directory_def; is_some_def; case_option_def; page_distinct;
      page_inj] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   MP_TAC (ISPEC `(a' : directory_page_data) x''` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (SPEC `a'' : directory_contents` directory_contents_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_directory_contents_def] THEN
   FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `a''' : physical_page_address` th)) THEN
   REWRITE_TAC [is_page_directory_or_table_def; is_page_table_def] THEN
   MP_TAC (SPEC `status s a'''` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' a'''` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_page_table_def; is_some_def; case_option_def; page_distinct;
      page_inj] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REFL_TAC);;

export_thm translate_page_inj;;

let status_translate_page = prove
  (`!s s'.
      status s = status s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_inj THEN
   ASM_REWRITE_TAC []);;

export_thm status_translate_page;;

let translate_page_reference_count = prove
  (`!s s'.
      translate_page s = translate_page s' ==>
      reference_count s = reference_count s'`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; reference_count_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm translate_page_reference_count;;

let cr3_is_page_directory = prove
  (`!s. wellformed s ==> is_page_directory (status s (cr3 s))`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` cr3_is_page_directory_def) THEN
   ASM_REWRITE_TAC []);;

export_thm cr3_is_page_directory;;

let environment_only_kernel_addresses = prove
  (`!s pd vpa ppa.
      wellformed s /\
      translate_page s pd vpa = SOME ppa /\
      is_environment (status s ppa) ==>
      is_kernel_page_address vpa`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` reference_maps_kernel_addresses_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   MP_TAC (SPEC `s : state` environment_only_in_reference_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`pd : page_directory`;
                               `vpa : virtual_page_address`]) THEN
   ASM_REWRITE_TAC [case_option_def]);;

export_thm environment_only_kernel_addresses;;

let page_directories_contain_reference = prove
  (`!s pd vpa.
      wellformed s /\
      is_page_directory (status s pd) /\
      is_kernel_page_address vpa ==>
      translate_page s pd vpa = translate_page s (reference s) vpa`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` page_directories_contain_reference_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm page_directories_contain_reference;;

let translate_page_environment_reference = prove
  (`!s pd vpa ppa.
      wellformed s /\
      translate_page s pd vpa = SOME ppa /\
      is_environment (status s ppa) ==>
      translate_page s (reference s) vpa = SOME ppa`,
   REWRITE_TAC [wellformed_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : state` page_directories_contain_reference_def) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`pd : page_directory`;
                               `vpa : virtual_page_address`]) THEN
   COND_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC translate_page_is_page_directory THEN
     EXISTS_TAC `vpa : virtual_page_address` THEN
     ASM_REWRITE_TAC [is_some_def];
     MATCH_MP_TAC environment_only_kernel_addresses THEN
     EXISTS_TAC `s : state` THEN
     EXISTS_TAC `pd : page_directory` THEN
     EXISTS_TAC `ppa : physical_page_address` THEN
     ASM_REWRITE_TAC [wellformed_def]];
    DISCH_THEN (fun th -> ASM_REWRITE_TAC [GSYM th])]);;

export_thm translate_page_environment_reference;;

let reference_count_environment = prove
  (`!s pd ppa.
      wellformed s /\
      is_page_directory (status s pd) /\
      is_environment (status s ppa) ==>
      reference_count s pd ppa = reference_count s (reference s) ppa`,
   REWRITE_TAC [reference_count_def] THEN
   REPEAT STRIP_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [EXTENSION; IN_ELIM] THEN
   GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    MATCH_MP_TAC translate_page_environment_reference THEN
    EXISTS_TAC `pd : page_directory` THEN
    ASM_REWRITE_TAC [];
    DISCH_THEN (fun th -> ASSUME_TAC th THEN REWRITE_TAC [GSYM th]) THEN
    MATCH_MP_TAC page_directories_contain_reference THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC environment_only_kernel_addresses THEN
    EXISTS_TAC `s : state` THEN
    EXISTS_TAC `reference s` THEN
    EXISTS_TAC `ppa : physical_page_address` THEN
    ASM_REWRITE_TAC []]);;

export_thm reference_count_environment;;

let write_e_status = prove
  (`!s s' va b ppa.
      write_e va b s s' /\
      (~is_environment (status s ppa) \/
       ~is_environment (status s' ppa)) ==>
      status s ppa = status s' ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [write_e_def] THEN
   DISCH_THEN
     (fun th ->
        STRIP_ASSUME_TAC (CONJUNCT1 th) THEN
        MP_TAC (CONJUNCT2 th)) THEN
   PAT_ASSUM `case_option X (Y : A -> B) Z` THEN
   MP_TAC (ISPEC `translation s va` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPEC `a : physical_address` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> MP_TAC (SPEC `ppa : physical_page_address` th)) THEN
   bool_cases_tac' `ppa : physical_page_address = x` THENL
   [ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]);
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s x` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' x` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_environment_def; dest_environment_def; case_option_def; page_distinct;
      page_inj; option_distinct; is_some_def]);;

export_thm write_e_status;;

let write_e_translate_page = prove
  (`!s s' va b.
      write_e va b s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_inj THEN
   GEN_TAC THEN
   DISCH_THEN ASSUME_TAC THEN
   MATCH_MP_TAC write_e_status THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_page_directory_or_table_def; is_page_directory_def;
      is_page_table_def; dest_page_directory_def; is_some_def;
      dest_page_table_def; dest_environment_def; case_option_def; page_distinct;
      page_inj; option_distinct; is_environment_def]);;

export_thm write_e_translate_page;;

let write_e_cr3 = prove
  (`!s s' va b. write_e va b s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [write_e_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_e_cr3;;

let write_e_regions = prove
  (`!s s' va b. write_e va b s s' ==> regions s = regions s'`,
   REWRITE_TAC [write_e_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_e_regions;;

let write_e_reference = prove
  (`!s s' va b. write_e va b s s' ==> reference s = reference s'`,
   REWRITE_TAC [write_e_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_e_reference;;

let write_e_translate_page_cr3 = prove
  (`!s s' va b.
      write_e va b s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_e_translate_page_cr3;;

let write_e_dest_normal = prove
  (`!s s' va b ppa.
      write_e va b s s' ==>
      dest_normal (status s ppa) = dest_normal (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `ppa : physical_page_address`]
      write_e_status) THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_normal_def; dest_environment_def; case_option_def; page_distinct;
      is_some_def; page_inj; option_distinct; is_environment_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_e_dest_normal;;

let write_e_reference_count = prove
  (`!s s' va b.
      write_e va b s s' ==>
      reference_count s = reference_count s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_reference_count THEN
   MATCH_MP_TAC write_e_translate_page THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC []);;

export_thm write_e_reference_count;;

let write_e_reference_count_cr3 = prove
  (`!s s' va b.
      write_e va b s s' ==>
      reference_count s (cr3 s) = reference_count s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_reference_count) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_e_reference_count_cr3;;

let derive_region_h_cr3 = prove
  (`!s s' pr ppa l. derive_region_h pr ppa l s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [derive_region_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm derive_region_h_cr3;;

let derive_region_h_status = prove
  (`!s s' pr ppa l. derive_region_h pr ppa l s s' ==> status s = status s'`,
   REWRITE_TAC [derive_region_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm derive_region_h_status;;

let derive_region_h_reference = prove
  (`!s s' pr ppa l.
      derive_region_h pr ppa l s s' ==> reference s = reference s'`,
   REWRITE_TAC [derive_region_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm derive_region_h_reference;;

let derive_region_h_translate_page = prove
  (`!s s' pr ppa l.
      derive_region_h pr ppa l s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC status_translate_page THEN
   MATCH_MP_TAC derive_region_h_status THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `ppa : physical_page_address` THEN
   EXISTS_TAC `l : region_length` THEN
   ASM_REWRITE_TAC []);;

export_thm derive_region_h_translate_page;;

let derive_region_h_translate_page_cr3 = prove
  (`!s s' pr ppa l.
      derive_region_h pr ppa l s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm derive_region_h_translate_page_cr3;;

let derive_region_h_reference_count = prove
  (`!s s' pr ppa l.
      derive_region_h pr ppa l s s' ==>
      reference_count s = reference_count s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_reference_count THEN
   MATCH_MP_TAC derive_region_h_translate_page THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `ppa : physical_page_address` THEN
   EXISTS_TAC `l : region_length` THEN
   ASM_REWRITE_TAC []);;

export_thm derive_region_h_reference_count;;

let derive_region_h_reference_count_cr3 = prove
  (`!s s' pr ppa l.
      derive_region_h pr ppa l s s' ==>
      reference_count s (cr3 s) = reference_count s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_reference_count) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm derive_region_h_reference_count_cr3;;

let allocate_page_directory_h_cr3 = prove
  (`!s s' ppa. allocate_page_directory_h ppa s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [allocate_page_directory_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm allocate_page_directory_h_cr3;;

let allocate_page_directory_h_reference = prove
  (`!s s' ppa.
      allocate_page_directory_h ppa s s' ==> reference s = reference s'`,
   REWRITE_TAC [allocate_page_directory_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm allocate_page_directory_h_reference;;

let allocate_page_directory_h_regions = prove
  (`!s s' ppa. allocate_page_directory_h ppa s s' ==> regions s = regions s'`,
   REWRITE_TAC [allocate_page_directory_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm allocate_page_directory_h_regions;;

(***
let allocate_page_directory_h_translate_page = prove
  (`!s s' pd ppa.
      allocate_page_directory_h ppa s s' ==>
      translate_page s' pd =
      translate_page s (if pd = ppa then reference s else pd)`,
   REWRITE_TAC [allocate_page_directory_h_def] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   MP_TAC (ISPEC `x : virtual_page_address` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   COND_CASES_TAC

   bool_cases_tac `(pd : page_directory) = ppa` THENL
   [
   REWRITE_TAC [translate_page_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_


   MATCH_MP_TAC status_translate_page THEN
   MATCH_MP_TAC allocate_page_directory_h_status THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `ppa : physical_page_address` THEN
   EXISTS_TAC `l : region_length` THEN
   ASM_REWRITE_TAC []);;

export_thm allocate_page_directory_h_translate_page;;

let allocate_page_directory_h_translate_page_cr3 = prove
  (`!s s' ppa.
      allocate_page_directory_h ppa s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      allocate_page_directory_h_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      allocate_page_directory_h_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm allocate_page_directory_h_translate_page_cr3;;

let allocate_page_directory_h_reference_count = prove
  (`!s s' ppa.
      allocate_page_directory_h ppa s s' ==>
      reference_count s = reference_count s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_reference_count THEN
   MATCH_MP_TAC allocate_page_directory_h_translate_page THEN
   EXISTS_TAC `pr : physical_region` THEN
   EXISTS_TAC `ppa : physical_page_address` THEN
   EXISTS_TAC `l : region_length` THEN
   ASM_REWRITE_TAC []);;

export_thm allocate_page_directory_h_reference_count;;

let allocate_page_directory_h_reference_count_cr3 = prove
  (`!s s' ppa.
      allocate_page_directory_h ppa s s' ==>
      reference_count s (cr3 s) = reference_count s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      allocate_page_directory_h_reference_count) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      allocate_page_directory_h_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm allocate_page_directory_h_reference_count_cr3;;
***)

let execute_h_status = prove
  (`!s s' pd. execute_h pd s s' ==> status s = status s'`,
   REWRITE_TAC [execute_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm execute_h_status;;

let execute_h_reference = prove
  (`!s s' pd.
      execute_h pd s s' ==> reference s = reference s'`,
   REWRITE_TAC [execute_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm execute_h_reference;;

let execute_h_regions = prove
  (`!s s' pd. execute_h pd s s' ==> regions s = regions s'`,
   REWRITE_TAC [execute_h_def] THEN
   REPEAT STRIP_TAC);;

export_thm execute_h_regions;;

let execute_h_translate_page = prove
  (`!s s' pd.
      execute_h pd s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC status_translate_page THEN
   MATCH_MP_TAC execute_h_status THEN
   EXISTS_TAC `pd : page_directory` THEN
   ASM_REWRITE_TAC []);;

export_thm execute_h_translate_page;;

let execute_h_reference_count = prove
  (`!s s' pd.
      execute_h pd s s' ==>
      reference_count s = reference_count s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_reference_count THEN
   MATCH_MP_TAC execute_h_translate_page THEN
   EXISTS_TAC `pd : page_directory` THEN
   ASM_REWRITE_TAC []);;

export_thm execute_h_reference_count;;

let write_k_status = prove
  (`!s s' va b ppa.
      write_k va b s s' /\
      (~is_normal (status s ppa) \/
       ~is_normal (status s' ppa)) ==>
      status s ppa = status s' ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [write_k_def] THEN
   DISCH_THEN
     (fun th ->
        STRIP_ASSUME_TAC (CONJUNCT1 th) THEN
        MP_TAC (CONJUNCT2 th)) THEN
   PAT_ASSUM `case_option X (Y : A -> B) Z` THEN
   MP_TAC (ISPEC `translation s va` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPEC `a : physical_address` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> MP_TAC (SPEC `ppa : physical_page_address` th)) THEN
   bool_cases_tac' `ppa : physical_page_address = x` THENL
   [ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]);
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s x` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' x` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_normal_def; dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; is_some_def]);;

export_thm write_k_status;;

let write_k_translate_page = prove
  (`!s s' va b.
      write_k va b s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_inj THEN
   GEN_TAC THEN
   DISCH_THEN ASSUME_TAC THEN
   MATCH_MP_TAC write_k_status THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_page_directory_or_table_def; is_page_directory_def;
      is_page_table_def; dest_page_directory_def; is_some_def;
      dest_page_table_def; dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; is_normal_def]);;

export_thm write_k_translate_page;;

let write_k_cr3 = prove
  (`!s s' va b. write_k va b s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [write_k_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_k_cr3;;

let write_k_regions = prove
  (`!s s' va b. write_k va b s s' ==> regions s = regions s'`,
   REWRITE_TAC [write_k_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_k_regions;;

let write_k_reference = prove
  (`!s s' va b. write_k va b s s' ==> reference s = reference s'`,
   REWRITE_TAC [write_k_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_k_reference;;

let write_k_translate_page_cr3 = prove
  (`!s s' va b.
      write_k va b s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_k_translate_page_cr3;;

let write_k_dest_environment = prove
  (`!s s' va b ppa.
      write_k va b s s' ==>
      dest_environment (status s ppa) = dest_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `ppa : physical_page_address`]
      write_k_status) THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_normal_def; dest_environment_def; case_option_def; page_distinct;
      is_some_def; page_inj; option_distinct; is_normal_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_k_dest_environment;;

let write_k_reference_count = prove
  (`!s s' va b.
      write_k va b s s' ==>
      reference_count s = reference_count s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_reference_count THEN
   MATCH_MP_TAC write_k_translate_page THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC []);;

export_thm write_k_reference_count;;

let write_k_reference_count_cr3 = prove
  (`!s s' va b.
      write_k va b s s' ==>
      reference_count s (cr3 s) = reference_count s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_reference_count) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_k_reference_count_cr3;;

let write_u_status = prove
  (`!s s' va b ppa.
      write_u va b s s' /\
      (~is_normal (status s ppa) \/
       ~is_normal (status s' ppa)) ==>
      status s ppa = status s' ppa`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [write_u_def] THEN
   DISCH_THEN
     (fun th ->
        STRIP_ASSUME_TAC (CONJUNCT1 th) THEN
        MP_TAC (CONJUNCT2 th)) THEN
   PAT_ASSUM `case_option X (Y : A -> B) Z` THEN
   MP_TAC (ISPEC `translation s va` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPEC `a : physical_address` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> MP_TAC (SPEC `ppa : physical_page_address` th)) THEN
   bool_cases_tac' `ppa : physical_page_address = x` THENL
   [ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]);
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s x` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' x` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_normal_def; dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; is_some_def]);;

export_thm write_u_status;;

let write_u_translate_page = prove
  (`!s s' va b.
      write_u va b s s' ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_inj THEN
   GEN_TAC THEN
   DISCH_THEN ASSUME_TAC THEN
   MATCH_MP_TAC write_u_status THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_page_directory_or_table_def; is_page_directory_def;
      is_page_table_def; dest_page_directory_def; is_some_def;
      dest_page_table_def; dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; is_normal_def]);;

export_thm write_u_translate_page;;

let write_u_cr3 = prove
  (`!s s' va b. write_u va b s s' ==> cr3 s = cr3 s'`,
   REWRITE_TAC [write_u_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_u_cr3;;

let write_u_regions = prove
  (`!s s' va b. write_u va b s s' ==> regions s = regions s'`,
   REWRITE_TAC [write_u_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_u_regions;;

let write_u_reference = prove
  (`!s s' va b. write_u va b s s' ==> reference s = reference s'`,
   REWRITE_TAC [write_u_def] THEN
   REPEAT STRIP_TAC);;

export_thm write_u_reference;;

let write_u_translate_page_cr3 = prove
  (`!s s' va b.
      write_u va b s s' ==>
      translate_page s (cr3 s) = translate_page s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_translate_page) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_u_translate_page_cr3;;

let write_u_dest_environment = prove
  (`!s s' va b ppa.
      write_u va b s s' ==>
      dest_environment (status s ppa) = dest_environment (status s' ppa)`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `ppa : physical_page_address`]
      write_u_status) THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s ppa` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' ppa` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_normal_def; dest_environment_def; case_option_def; page_distinct;
      is_some_def; page_inj; option_distinct; is_normal_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_u_dest_environment;;

let write_u_reference_count = prove
  (`!s s' va b.
      write_u va b s s' ==>
      reference_count s = reference_count s'`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC translate_page_reference_count THEN
   MATCH_MP_TAC write_u_translate_page THEN
   EXISTS_TAC `va : virtual_address` THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC []);;

export_thm write_u_reference_count;;

let write_u_reference_count_cr3 = prove
  (`!s s' va b.
      write_u va b s s' ==>
      reference_count s (cr3 s) = reference_count s' (cr3 s')`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_reference_count) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

export_thm write_u_reference_count_cr3;;

let local_respect_write_e_view_u = prove
  (`!s s' va b. write_e va b s s' ==> view_u s = view_u s'`,
   REWRITE_TAC [view_u_def; u_view_inj] THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `x : physical_page_address`]
      write_e_dest_normal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; option_inj; PAIR_EQ] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_e_reference_count_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

let local_respect_derive_region_h_view_e = prove
  (`!s s' pr ppa l. derive_region_h pr ppa l s s' ==> view_e s = view_e s'`,
   REWRITE_TAC [view_e_def; e_view_inj] THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_status) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; option_inj; PAIR_EQ] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_reference_count_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

(***
let local_respect_allocate_page_directory_h_view_e = prove
  (`!s s' ppa. allocate_page_directory_h ppa s s' ==> view_e s = view_e s'`,
   REWRITE_TAC [view_e_def; e_view_inj] THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_status) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; option_inj; PAIR_EQ] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `pr : physical_region`;
             `ppa : physical_page_address`; `l : region_length`]
      derive_region_h_reference_count_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;
***)

let local_respect_execute_h_view_e = prove
  (`!s s' pd.
      wellformed s /\ wellformed s' /\ execute_h pd s s' ==>
      view_e s = view_e s'`,
   REWRITE_TAC [view_e_def; e_view_inj] THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   bool_cases_tac' `is_kernel_page_address x` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `NONE : (page_data # reference_count) option` THEN
    CONJ_TAC THENL
    [MP_TAC (ISPEC `translate_page s (cr3 s) x` option_cases) THEN
     STRIP_TAC THENL
     [ASM_REWRITE_TAC [case_option_def];
      ASM_REWRITE_TAC [case_option_def] THEN
      KNOW_TAC `~is_environment (status s a)` THENL
      [STRIP_TAC THEN
       UNDISCH_TAC `~is_kernel_page_address x` THEN
       REWRITE_TAC [] THEN
       MATCH_MP_TAC environment_only_kernel_addresses THEN
       EXISTS_TAC `s : state` THEN
       EXISTS_TAC `cr3 s` THEN
       EXISTS_TAC `a : physical_page_address` THEN
       ASM_REWRITE_TAC [];
       ALL_TAC] THEN
       MP_TAC (SPEC `status s a` page_cases) THEN
       STRIP_TAC THEN
       ASM_REWRITE_TAC
         [dest_environment_def; case_option_def; page_distinct;
          page_inj; option_distinct; is_some_def; is_environment_def]];
     MP_TAC (ISPEC `translate_page s' (cr3 s') x` option_cases) THEN
     STRIP_TAC THENL
     [ASM_REWRITE_TAC [case_option_def];
      ASM_REWRITE_TAC [case_option_def] THEN
      KNOW_TAC `~is_environment (status s' a)` THENL
      [STRIP_TAC THEN
       UNDISCH_TAC `~is_kernel_page_address x` THEN
       REWRITE_TAC [] THEN
       MATCH_MP_TAC environment_only_kernel_addresses THEN
       EXISTS_TAC `s' : state` THEN
       EXISTS_TAC `cr3 s'` THEN
       EXISTS_TAC `a : physical_page_address` THEN
       ASM_REWRITE_TAC [];
       ALL_TAC] THEN
       MP_TAC (SPEC `status s' a` page_cases) THEN
       STRIP_TAC THEN
       ASM_REWRITE_TAC
         [dest_environment_def; case_option_def; page_distinct;
          page_inj; option_distinct; is_some_def; is_environment_def]]];
    ALL_TAC] THEN
   MP_TAC (ISPEC `translate_page s (cr3 s) x` option_cases) THEN
   STRIP_TAC THEN
   MP_TAC (ISPEC `translate_page s' (cr3 s') x` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THENL
   [(* Case 1 *)
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_status) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
    UNDISCH_TAC `translate_page s' (cr3 s') x = SOME a` THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_translate_page) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
    STRIP_TAC THEN
    MP_TAC (SPEC `status s a` page_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [dest_environment_def; case_option_def; page_distinct;
       page_inj; option_distinct; is_some_def] THEN
    MP_TAC (SPECL [`s : state`; `cr3 s'`;
                   `x : virtual_page_address`; `a : physical_page_address`]
              translate_page_environment_reference) THEN
    ASM_REWRITE_TAC
      [is_environment_def; dest_environment_def; is_some_def] THEN
    SUFF_TAC `translate_page s (cr3 s) x =
              translate_page s (reference s) x` THENL
    [DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
     ASM_REWRITE_TAC [option_distinct];
     ALL_TAC] THEN
    MATCH_MP_TAC page_directories_contain_reference THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC cr3_is_page_directory THEN
    ASM_REWRITE_TAC [];

    (* Case 2 *)
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_status) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    UNDISCH_TAC `translate_page s (cr3 s) x = SOME a` THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_translate_page) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    STRIP_TAC THEN
    MP_TAC (SPEC `status s' a` page_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [dest_environment_def; case_option_def; page_distinct;
       page_inj; option_distinct; is_some_def] THEN
    MP_TAC (SPECL [`s' : state`; `cr3 s`;
                   `x : virtual_page_address`; `a : physical_page_address`]
              translate_page_environment_reference) THEN
    ASM_REWRITE_TAC
      [is_environment_def; dest_environment_def; is_some_def] THEN
    SUFF_TAC `translate_page s' (cr3 s') x =
              translate_page s' (reference s') x` THENL
    [DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
     ASM_REWRITE_TAC [option_distinct];
     ALL_TAC] THEN
    MATCH_MP_TAC page_directories_contain_reference THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC cr3_is_page_directory THEN
    ASM_REWRITE_TAC [];

    (* Case 3 *)
    POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN
    MP_TAC (SPECL [`s : state`; `cr3 s`; `x : virtual_page_address`]
              page_directories_contain_reference) THEN
    COND_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC cr3_is_page_directory THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC (SPECL [`s' : state`; `cr3 s'`; `x : virtual_page_address`]
              page_directories_contain_reference) THEN
    COND_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC cr3_is_page_directory THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_status) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_translate_page) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
    MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
              execute_h_reference) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
    ASM_REWRITE_TAC [option_inj] THEN
    DISCH_THEN (SUBST_VAR_TAC o GSYM) THEN
    MP_TAC (SPEC `status s a` page_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [dest_environment_def; case_option_def; page_distinct;
       page_inj; option_distinct; is_some_def; option_inj; PAIR_EQ] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `reference_count s (reference s) a` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC reference_count_environment THEN
     ASM_REWRITE_TAC [is_environment_def; dest_environment_def; is_some_def] THEN
     MATCH_MP_TAC cr3_is_page_directory THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `reference_count s' (reference s') a` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [reference_count_def] THEN
     MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
               execute_h_translate_page) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
     MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
               execute_h_reference) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]);
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC reference_count_environment THEN
    ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC cr3_is_page_directory THEN
     ASM_REWRITE_TAC [];
     MP_TAC (SPECL [`s : state`; `s' : state`; `pd : page_directory`]
               execute_h_status) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
     ASM_REWRITE_TAC
       [is_environment_def; dest_environment_def; is_some_def]]]);;

let local_respect_write_k_view_e = prove
  (`!s s' va b. write_k va b s s' ==> view_e s = view_e s'`,
   REWRITE_TAC [view_e_def; e_view_inj] THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `x : physical_page_address`]
      write_k_dest_environment) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; option_inj; PAIR_EQ] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_reference_count_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

let local_respect_write_k_view_h = prove
  (`!s s' va b. write_k va b s s' ==> view_h s = view_h s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [view_h_def; h_view_inj] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_reference) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_k_regions) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `x : physical_page_address`]
      write_k_status) THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s x` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' x` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_normal_def; is_some_def;
      dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; option_inj]);;

let local_respect_write_u_view_e = prove
  (`!s s' va b. write_u va b s s' ==> view_e s = view_e s'`,
   REWRITE_TAC [view_e_def; e_view_inj] THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_translate_page_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `x : physical_page_address`]
      write_u_dest_environment) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; option_inj; PAIR_EQ] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_reference_count_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]));;

let local_respect_write_u_view_h = prove
  (`!s s' va b. write_u va b s s' ==> view_h s = view_h s'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [view_h_def; h_view_inj] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_cr3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_reference) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`]
      write_u_regions) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   MP_TAC
     (SPECL [`s : state`; `s' : state`; `va : virtual_address`; `b : byte`;
             `x : physical_page_address`]
      write_u_status) THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `status s x` page_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `status s' x` page_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [is_normal_def; is_some_def;
      dest_normal_def; case_option_def; page_distinct;
      page_inj; option_distinct; option_inj]);;

(***
let local_respect = prove
  (`!s s' a u.
      ~interferes (domain a) u /\
      action a s s' ==>
      view_equiv u s s'`,
   REWRITE_TAC [action_def; view_equiv_def] THEN
   GEN_TAC THEN
   GEN_TAC THEN
   MATCH_MP_TAC action_induct THEN
   REPEAT CONJ_TAC THEN
   REPEAT GEN_TAC THEN
   SPEC_TAC (`u : domain`, `u : domain`) THEN
   MATCH_MP_TAC domain_induct THEN
   REPEAT CONJ_TAC THEN
   REWRITE_TAC
     [interferes_def; domain_def; action_spec_def; view_def; view_inj;
      domain_distinct] THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_e_view_u THEN
    EXISTS_TAC `a0 : virtual_address` THEN
    EXISTS_TAC `a1 : byte` THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_derive_region_h_view_e THEN
    EXISTS_TAC `a0 : physical_region` THEN
    EXISTS_TAC `a1 : physical_page_address` THEN
    EXISTS_TAC `a2 : region_length` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC;
    ALL_TAC;
    ALL_TAC;
    ALL_TAC;
    ALL_TAC;
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_execute_h_view_e THEN
    EXISTS_TAC `a : page_directory` THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_k_view_e THEN
    EXISTS_TAC `a0 : virtual_address` THEN
    EXISTS_TAC `a1 : byte` THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_k_view_h THEN
    EXISTS_TAC `a0 : virtual_address` THEN
    EXISTS_TAC `a1 : byte` THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_u_view_e THEN
    EXISTS_TAC `a0 : virtual_address` THEN
    EXISTS_TAC `a1 : byte` THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC local_respect_write_u_view_h THEN
    EXISTS_TAC `a0 : virtual_address` THEN
    EXISTS_TAC `a1 : byte` THEN
    ASM_REWRITE_TAC []]);;

export_thm local_respect;;

let weak_step_consistency = prove
  (`!s s' t t' a u.
      view_equiv u s t /\
      view_equiv (domain a) s t /\
      action a s s' /\
      action a t t' ==>
      view_equiv u s' t'`,
   REWRITE_TAC [action_def; view_equiv_def] THEN
   GEN_TAC THEN
   GEN_TAC THEN
   GEN_TAC THEN
   GEN_TAC THEN
   MATCH_MP_TAC action_induct THEN
   REPEAT CONJ_TAC THEN
   REPEAT GEN_TAC THEN
   SPEC_TAC (`u : domain`, `u : domain`) THEN
   MATCH_MP_TAC domain_induct THEN
   REPEAT CONJ_TAC THEN
   REWRITE_TAC [domain_def; action_spec_def; view_def; view_inj] THEN
   REWRITE_TAC [view_e_def; e_view_inj] THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   REWRITE_TAC [write_e_def] THEN
   CHEAT_TAC);;

export_thm weak_step_consistency;;

let output_consistency = prove
  (`!s s' t t' a.
      view_equiv (domain a) s t /\
      action a s s' /\
      action a t t' ==>
      view (domain a) s' = view (domain a) t'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [GSYM view_equiv_def] THEN
   MATCH_MP_TAC weak_step_consistency THEN
   EXISTS_TAC `s : state` THEN
   EXISTS_TAC `t : state` THEN
   EXISTS_TAC `a : action` THEN
   ASM_REWRITE_TAC []);;

export_thm output_consistency;;
***)

logfile_end ();;
