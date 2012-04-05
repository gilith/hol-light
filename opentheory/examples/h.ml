(* ========================================================================= *)
(* Memory safety for the H interface.                                        *)
(* Joe Hurd and Rebekah Leslie                                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of the H interface.                                            *)
(* ------------------------------------------------------------------------- *)

logfile "h-def";;

(* Reference counts *)

let reference_count_tybij =
  mk_newtype ("c","reference_count") ("n",`:num`);;

export_thm reference_count_tybij;;

(* Region lengths *)

let region_length_tybij =
  mk_newtype ("l","region_length") ("n",`:num`);;

export_thm region_length_tybij;;

(* ------------------------------------------------------------------------- *)
(* Address offsets.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Superpage offsets *)

let superpage_offset_tybij =
  mk_newtype ("si","superpage_offset") ("w",`:word10`);;

export_thm superpage_offset_tybij;;

let num_to_superpage_offset_def = new_definition
  `!n.
     num_to_superpage_offset n =
     mk_superpage_offset (num_to_word10 n)`;;

export_thm num_to_superpage_offset_def;;

let superpage_offset_add_def = new_definition
  `!si n.
     superpage_offset_add si n =
     mk_superpage_offset
       (word10_add (dest_superpage_offset si) (num_to_word10 n))`;;

export_thm superpage_offset_add_def;;

(* Page offsets *)

let page_offset_tybij =
  mk_newtype ("i","page_offset") ("w",`:word12`);;

export_thm page_offset_tybij;;

(* ------------------------------------------------------------------------- *)
(* Physical addresses.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Physical superpage addresses *)

let physical_superpage_address_tybij =
  mk_newtype ("psa","physical_superpage_address") ("w",`:word10`);;

export_thm physical_superpage_address_tybij;;

let num_to_physical_superpage_address_def = new_definition
  `!n.
     num_to_physical_superpage_address n =
     mk_physical_superpage_address (num_to_word10 n)`;;

export_thm num_to_physical_superpage_address_def;;

let physical_superpage_address_add_def = new_definition
  `!psa n.
     physical_superpage_address_add psa n =
     mk_physical_superpage_address
       (word10_add (dest_physical_superpage_address psa) (num_to_word10 n))`;;

export_thm physical_superpage_address_add_def;;

(* Physical page addresses *)

let physical_page_address_tybij =
  mk_newtype ("ppa","physical_page_address")
    ("r", `:physical_superpage_address # superpage_offset`);;

export_thm physical_page_address_tybij;;

let physical_page_address_suc_def = new_definition
  `!ppa.
     physical_page_address_suc ppa =
     let (psa,si) = dest_physical_page_address ppa in
     let si' = superpage_offset_add si 1 in
     let psa' =
         if si' = num_to_superpage_offset 0 then
           physical_superpage_address_add psa 1
         else
           psa in
     mk_physical_page_address (psa',si')`;;

export_thm physical_page_address_suc_def;;

let physical_page_address_add_def = new_recursive_definition num_RECURSION
  `(!ppa. physical_page_address_add ppa 0 = ppa) /\
   (!ppa n.
      physical_page_address_add ppa (SUC n) =
      physical_page_address_add (physical_page_address_suc ppa) n)`;;

export_thm physical_page_address_add_def;;

(* Physical addresses *)

let physical_address_tybij =
  mk_newtype ("pa","physical_address")
    ("r", `:physical_page_address # page_offset`);;

export_thm physical_address_tybij;;

(* ------------------------------------------------------------------------- *)
(* Regions of physical memory.                                               *)
(* ------------------------------------------------------------------------- *)

let (physical_region_induct,physical_region_recursion) = define_type
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
     MAP (physical_page_address_add s) (interval 0 (dest_region_length l))`;;

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

(* ------------------------------------------------------------------------- *)
(* Virtual addresses.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Virtual superpage addresses *)

let virtual_superpage_address_tybij =
  mk_newtype ("vsa","virtual_superpage_address") ("w",`:word10`);;

export_thm virtual_superpage_address_tybij;;

let num_to_virtual_superpage_address_def = new_definition
  `!n.
     num_to_virtual_superpage_address n =
     mk_virtual_superpage_address (num_to_word10 n)`;;

export_thm num_to_virtual_superpage_address_def;;

let virtual_superpage_address_add_def = new_definition
  `!vsa n.
     virtual_superpage_address_add vsa n =
     mk_virtual_superpage_address
       (word10_add (dest_virtual_superpage_address vsa) (num_to_word10 n))`;;

export_thm virtual_superpage_address_add_def;;

(* Virtual page addresses *)

let virtual_page_address_tybij =
  mk_newtype ("vpa","virtual_page_address")
    ("r", `:virtual_superpage_address # superpage_offset`);;

export_thm virtual_page_address_tybij;;

let virtual_page_address_suc_def = new_definition
  `!vpa.
     virtual_page_address_suc vpa =
     let (vsa,si) = dest_virtual_page_address vpa in
     let si' = superpage_offset_add si 1 in
     let vsa' =
         if si' = num_to_superpage_offset 0 then
           virtual_superpage_address_add vsa 1
         else
           vsa in
     mk_virtual_page_address (vsa',si')`;;

export_thm virtual_page_address_suc_def;;

let virtual_page_address_add_def = new_recursive_definition num_RECURSION
    `(!vpa. virtual_page_address_add vpa 0 = vpa) /\
     (!vpa n.
        virtual_page_address_add vpa (SUC n) =
        virtual_page_address_add (virtual_page_address_suc vpa) n)`;;

export_thm virtual_page_address_add_def;;

(* Virtual addresses *)

let virtual_address_tybij =
  mk_newtype ("va","virtual_address")
    ("r", `:virtual_page_address # page_offset`);;

export_thm virtual_address_tybij;;

(* ------------------------------------------------------------------------- *)
(* Regions of virtual memory.                                                *)
(* ------------------------------------------------------------------------- *)

let (virtual_region_induct,virtual_region_recursion) = define_type
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
     MAP (virtual_page_address_add s) (interval 0 (dest_region_length l))`;;

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

(* ------------------------------------------------------------------------- *)
(* User and kernel virtual addresses.                                        *)
(* ------------------------------------------------------------------------- *)

let is_kernel_superpage_address_def = new_definition
  `!vsa.
     is_kernel_superpage_address vsa <=>
     let w = dest_virtual_superpage_address vsa in
     word10_bit w 9 /\ word10_bit w 8`;;

export_thm is_kernel_superpage_address_def;;

let is_user_superpage_address_def = new_definition
  `!vsa.
     is_user_superpage_address vsa <=>
     ~is_kernel_superpage_address vsa`;;

export_thm is_user_superpage_address_def;;

let is_kernel_page_address_def = new_definition
  `!vpa.
     is_kernel_page_address vpa <=>
     let (vsa,si) = dest_virtual_page_address vpa in
     is_kernel_superpage_address vsa`;;

export_thm is_kernel_page_address_def;;

let is_user_page_address_def = new_definition
  `!vpa.
     is_user_page_address vpa <=>
     ~is_kernel_page_address vpa`;;

export_thm is_user_page_address_def;;

let is_kernel_address_def = new_definition
  `!va.
     is_kernel_address va <=>
     let (vpa,i) = dest_virtual_address va in
     is_kernel_page_address vpa`;;

export_thm is_kernel_address_def;;

let is_user_address_def = new_definition
  `!va.
     is_user_address va <=>
     ~is_kernel_address va`;;

export_thm is_user_address_def;;

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

(* ------------------------------------------------------------------------- *)
(* Page data.                                                                *)
(* ------------------------------------------------------------------------- *)

let page_data_tybij =
  mk_newtype ("d","page_data")
    ("f", `:page_offset -> byte`);;

export_thm page_data_tybij;;

let zero_page_data_def = new_definition
  `zero_page_data = mk_page_data (\i. num_to_byte 0)`;;

export_thm zero_page_data_def;;

let update_page_data_def = new_definition
  `!k v d.
      update_page_data k v d =
      mk_page_data (\i. if i = k then v else dest_page_data d i)`;;

export_thm update_page_data_def;;

(* ------------------------------------------------------------------------- *)
(* Page tables.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Page tables *)

new_type_abbrev("page_table",`:physical_page_address`);;

(* Page table data *)

new_type_abbrev("page_table_index",`:superpage_offset`);;

let page_table_data_tybij =
  mk_newtype ("t","page_table_data")
    ("f", `:page_table_index -> physical_page_address option`);;

export_thm page_table_data_tybij;;

(* ------------------------------------------------------------------------- *)
(* Page directories.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Page directories *)

new_type_abbrev("page_directory",`:physical_page_address`);;

(* Page directory entries *)

let (page_directory_entry_induct,
     page_directory_entry_recursion) = define_type
    "page_directory_entry =
       Superpage physical_superpage_address
     | Table page_table";;

export_thm page_directory_entry_induct;;
export_thm page_directory_entry_recursion;;

let case_page_directory_entry_def =
  new_recursive_definition page_directory_entry_recursion
  `(!f g psa. case_page_directory_entry f g (Superpage psa) = (f psa : A)) /\
   (!f g pt. case_page_directory_entry f g (Table pt) = (g pt : A))`;;

export_thm case_page_directory_entry_def;;

(* Page directory data *)

new_type_abbrev("page_directory_index",`:virtual_superpage_address`);;

let page_directory_data_tybij =
  mk_newtype ("d","page_directory_data")
    ("f", `:page_directory_index -> page_directory_entry option`);;

export_thm page_directory_data_tybij;;

(* ------------------------------------------------------------------------- *)
(* Page types.                                                               *)
(* ------------------------------------------------------------------------- *)

let (page_induct,page_recursion) = define_type
    "page =
       Environment page_data
     | Normal page_data
     | PageDirectory page_directory_data
     | PageTable page_table_data
     | NotInstalled";;

export_thm page_induct;;
export_thm page_recursion;;

let dest_environment_def = new_recursive_definition page_recursion
  `(!d. dest_environment (Environment d) = SOME d) /\
   (!d. dest_environment (Normal d) = NONE) /\
   (!pdd. dest_environment (PageDirectory pdd) = NONE) /\
   (!ptd. dest_environment (PageTable ptd) = NONE) /\
   (dest_environment NotInstalled = NONE)`;;

export_thm dest_environment_def;;

let dest_normal_def = new_recursive_definition page_recursion
  `(!d. dest_normal (Environment d) = NONE) /\
   (!d. dest_normal (Normal d) = SOME d) /\
   (!pdd. dest_normal (PageDirectory pdd) = NONE) /\
   (!ptd. dest_normal (PageTable ptd) = NONE) /\
   (dest_normal NotInstalled = NONE)`;;

export_thm dest_normal_def;;

let dest_environment_or_normal_def = new_recursive_definition page_recursion
  `(!d. dest_environment_or_normal (Environment d) = SOME d) /\
   (!d. dest_environment_or_normal (Normal d) = SOME d) /\
   (!pdd. dest_environment_or_normal (PageDirectory pdd) = NONE) /\
   (!ptd. dest_environment_or_normal (PageTable ptd) = NONE) /\
   (dest_environment_or_normal NotInstalled = NONE)`;;

export_thm dest_environment_or_normal_def;;

let dest_page_directory_def = new_recursive_definition page_recursion
  `(!d. dest_page_directory (Environment d) = NONE) /\
   (!d. dest_page_directory (Normal d) = NONE) /\
   (!pdd. dest_page_directory (PageDirectory pdd) = SOME pdd) /\
   (!ptd. dest_page_directory (PageTable ptd) = NONE) /\
   (dest_page_directory NotInstalled = NONE)`;;

export_thm dest_page_directory_def;;

let dest_page_table_def = new_recursive_definition page_recursion
  `(!d. dest_page_table (Environment d) = NONE) /\
   (!d. dest_page_table (Normal d) = NONE) /\
   (!pdd. dest_page_table (PageDirectory pdd) = NONE) /\
   (!ptd. dest_page_table (PageTable ptd) = SOME ptd) /\
   (dest_page_table NotInstalled = NONE)`;;

export_thm dest_page_table_def;;

let is_not_installed_def = new_recursive_definition page_recursion
  `(!d. is_not_installed (Environment d) = F) /\
   (!d. is_not_installed (Normal d) = F) /\
   (!pdd. is_not_installed (PageDirectory pdd) = F) /\
   (!ptd. is_not_installed (PageTable ptd) = F) /\
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

(* ------------------------------------------------------------------------- *)
(* The state of the system.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Derived physical regions state *)

let (region_state_induct,region_state_recursion) = define_type
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

(* System state *)

let (state_induct,state_recursion) = define_type
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

let is_normal_page_def = new_definition
  `!s ppa. is_normal_page s ppa <=> is_normal (status s ppa)`;;

export_thm is_normal_page_def;;

(* ------------------------------------------------------------------------- *)
(* Virtual to physical mappings.                                             *)
(* ------------------------------------------------------------------------- *)

let translate_page_def = new_definition
  `!s pd vpa.
     translate_page s pd vpa =
     let (vsa,si) = dest_virtual_page_address vpa in
     case_option
       NONE
       (\pdd.
          case_option
            NONE
            (\pdc.
               case_page_directory_entry
                 (\psa. SOME (mk_physical_page_address (psa,si)))
                 (\pt.
                    case_option
                      NONE
                      (\ptd. dest_page_table_data ptd si)
                      (dest_page_table (status s pt)))
                 pdc)
            (dest_page_directory_data pdd vsa))
       (dest_page_directory (status s pd))`;;

export_thm translate_page_def;;

let translation_def = new_definition
  `!s va.
     translation s va =
     let (vpa,off) = dest_virtual_address va in
     case_option
       NONE
       (\ppa. SOME (mk_physical_address (ppa,off)))
       (translate_page s (cr3 s) vpa)`;;

export_thm translation_def;;

let reference_count_def = new_definition
  `!s pd ppa.
     reference_count s pd ppa =
     mk_reference_count (CARD { vpa | translate_page s pd vpa = SOME ppa })`;;

export_thm reference_count_def;;

let table_mapped_in_directory_def = new_definition
  `!s pd pt.
     table_mapped_in_directory s pd pt <=>
     case_option
       F
       (\pdd. ?pdi. dest_page_directory_data pdd pdi = SOME (Table pt))
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

let unmapped_normal_page_def = new_definition
  `!s ppa.
     unmapped_normal_page s ppa <=>
     unmapped_page s ppa /\ is_normal_page s ppa`;;

export_thm unmapped_normal_page_def;;

(* ------------------------------------------------------------------------- *)
(* Well-formed machine states.                                               *)
(* ------------------------------------------------------------------------- *)

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
              (\pdc.
                 case_page_directory_entry
                   (\spa. T)
                   (\ppa. is_page_table (status s ppa))
                   pdc)
              (dest_page_directory_data pdd pdi))
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

(* TODO *)
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

(* ------------------------------------------------------------------------- *)
(* Protection domains and their view of the system state.                    *)
(* ------------------------------------------------------------------------- *)

let (domain_induct,domain_recursion) = define_type
    "domain =
       EDomain
     | HDomain
     | KDomain
     | UDomain";;

export_thm domain_induct;;
export_thm domain_recursion;;

(* The view of the environment domain *)

let (e_view_induct,e_view_recursion) = define_type
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

(* The view of the H domain *)

let (h_view_induct,h_view_recursion) = define_type
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

(* The view of the kernel domain *)

let (k_view_induct,k_view_recursion) = define_type
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

(* The view of the user domain *)

let (u_view_induct,u_view_recursion) = define_type
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

(* A type of domain view *)

let (view_induct,view_recursion) = define_type
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

(* ------------------------------------------------------------------------- *)
(* Actions.                                                                  *)
(* ------------------------------------------------------------------------- *)

let (action_induct,action_recursion) = define_type
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

let write_e_def = new_definition
  `!va b s s'.
     write_e va b s s' <=>
     cr3 s = cr3 s' /\
     reference s = reference s' /\
     regions s = regions s' /\
     case_option
       F
       (\pa.
          let (ppa,off) = dest_physical_address pa in
          !ppa'.
            if ppa' = ppa then
              case_option
                F
                (\pd.
                   dest_environment (status s' ppa') =
                   SOME (update_page_data off b pd))
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
              (virtual_region_to_list vr) (physical_region_to_list pr)) /\
     !ppa.
       if table_mapped_in_directory s (reference s) ppa then
         is_page_table (status s' ppa)
       else
         status s ppa = status s' ppa`;;

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
       (\pa.
          let (ppa,off) = dest_physical_address pa in
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
       (\pa.
          let (ppa,off) = dest_physical_address pa in
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

(* ------------------------------------------------------------------------- *)
(* Output.                                                                   *)
(* ------------------------------------------------------------------------- *)

let output_tybij =
  mk_newtype ("x","output")
    ("v", `:view`);;

export_thm output_tybij;;

let output_def = new_definition
  `!a s. output a s = mk_output (view (domain a) s)`;;

export_thm output_def;;

(* ------------------------------------------------------------------------- *)
(* System security policy.                                                   *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Properties of the H interface.                                            *)
(* ------------------------------------------------------------------------- *)

logfile "h-thm";;

(* ------------------------------------------------------------------------- *)
(* Address offsets.                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Physical addresses.                                                       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Regions of physical memory.                                               *)
(* ------------------------------------------------------------------------- *)

let physical_region_cases = prove_cases_thm physical_region_induct;;

export_thm physical_region_cases;;

let physical_region_inj = injectivity "physical_region";;

(* ------------------------------------------------------------------------- *)
(* Virtual addresses.                                                        *)
(* ------------------------------------------------------------------------- *)

let virtual_superpage_address_cases = prove
  (`!vsa. ?w. vsa = mk_virtual_superpage_address w`,
   GEN_TAC THEN
   EXISTS_TAC `dest_virtual_superpage_address vsa` THEN
   REWRITE_TAC [virtual_superpage_address_tybij]);;

let virtual_superpage_address_cases_tac =
    CASES_TAC virtual_superpage_address_cases;;

let virtual_page_address_cases = prove
  (`!vpa. ?vsa si. vpa = mk_virtual_page_address (vsa,si)`,
   GEN_TAC THEN
   EXISTS_TAC `FST (dest_virtual_page_address vpa)` THEN
   EXISTS_TAC `SND (dest_virtual_page_address vpa)` THEN
   REWRITE_TAC [PAIR; virtual_page_address_tybij]);;

let virtual_page_address_cases_tac =
    CASES_TAC virtual_page_address_cases;;

(* ------------------------------------------------------------------------- *)
(* Regions of virtual memory.                                                *)
(* ------------------------------------------------------------------------- *)

let virtual_region_cases = prove_cases_thm virtual_region_induct;;

export_thm virtual_region_cases;;

let virtual_region_inj = injectivity "virtual_region";;

(* ------------------------------------------------------------------------- *)
(* User and kernel virtual addresses.                                        *)
(* ------------------------------------------------------------------------- *)

let kernel_page_address_not_user = prove
  (`!vpa. is_kernel_page_address vpa <=> ~is_user_page_address vpa`,
   REWRITE_TAC [is_user_page_address_def]);;

export_thm kernel_page_address_not_user;;

let user_kernel_boundary = prove
  (`!n.
      n < 768 ==>
      is_user_superpage_address (num_to_virtual_superpage_address n)`,
   GEN_TAC THEN
   SUBGOAL_THEN `768 < word10_size` ASSUME_TAC THENL
   [REWRITE_TAC [word10_size_def; word10_width_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN
   REWRITE_TAC
     [is_user_superpage_address_def; is_kernel_superpage_address_def;
      LET_DEF; LET_END_DEF; num_to_virtual_superpage_address_def;
      virtual_superpage_address_tybij] THEN
   MP_TAC (SPEC `n : num` num_to_word10_to_num_bound) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `768` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (fun th -> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [SYM th])) THEN
   MP_TAC (SPEC `768` num_to_word10_to_num_bound) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [GSYM word10_lt_def] THEN
   MP_TAC (SPEC `num_to_word10 n` word10_list_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN
   bit_blast_tac THEN
   REWRITE_TAC [DE_MORGAN_THM]);;

export_thm user_kernel_boundary;;

(* ------------------------------------------------------------------------- *)
(* Page data.                                                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Page tables.                                                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Page directories.                                                         *)
(* ------------------------------------------------------------------------- *)

let page_directory_entry_cases = prove_cases_thm page_directory_entry_induct;;

export_thm page_directory_entry_cases;;

let page_directory_entry_distinct = distinctness "page_directory_entry";;

let page_directory_entry_inj = injectivity "page_directory_entry";;

(* ------------------------------------------------------------------------- *)
(* Page types.                                                               *)
(* ------------------------------------------------------------------------- *)

let page_cases = prove
  (`!p.
      (?d. p = Environment d) \/
      (?d. p = Normal d) \/
      (?pdd. p = PageDirectory pdd) \/
      (?ptd. p = PageTable ptd) \/
      p = NotInstalled`,
   ACCEPT_TAC (prove_cases_thm page_induct));;

export_thm page_cases;;

let page_cases_tac = CASES_TAC page_cases;;

let page_distinct = distinctness "page";;

let page_inj = injectivity "page";;

(* ------------------------------------------------------------------------- *)
(* The state of the system.                                                  *)
(* ------------------------------------------------------------------------- *)

let region_state_cases = prove_cases_thm region_state_induct;;

export_thm region_state_cases;;

let region_state_inj = injectivity "region_state";;

let state_cases = prove_cases_thm state_induct;;

export_thm state_cases;;

let state_inj = injectivity "state";;

(* ------------------------------------------------------------------------- *)
(* Virtual to physical mappings.                                             *)
(* ------------------------------------------------------------------------- *)

let translate_page_eq = prove
  (`!s s'.
      (!pd vpa.
         translate_page s pd vpa =
         translate_page s' pd vpa) ==>
      translate_page s = translate_page s'`,
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [FUN_EQ_THM]);;

export_thm translate_page_eq;;

let translate_page_is_page_directory = prove
  (`!s pd vpa.
      is_some (translate_page s pd vpa) ==>
      is_page_directory (status s pd)`,
   REPEAT GEN_TAC THEN
   virtual_page_address_cases_tac `vpa : virtual_page_address` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [translate_page_def; virtual_page_address_tybij] THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   page_cases_tac `status s pd` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [dest_page_directory_def; is_page_directory_def; is_some_def;
      case_option_def]);;

export_thm translate_page_is_page_directory;;

(* ------------------------------------------------------------------------- *)
(* Well-formed machine states.                                               *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Protection domains and their view of the system state.                    *)
(* ------------------------------------------------------------------------- *)

let domain_cases = prove_cases_thm domain_induct;;

export_thm domain_cases;;

let domain_distinct = distinctness "domain";;

let action_cases = prove_cases_thm action_induct;;

export_thm action_cases;;

let action_distinct = distinctness "action";;

let action_inj = injectivity "action";;

let e_view_cases = prove_cases_thm e_view_induct;;

export_thm e_view_cases;;

let e_view_inj = injectivity "e_view";;

let h_view_cases = prove_cases_thm h_view_induct;;

export_thm h_view_cases;;

let h_view_inj = injectivity "h_view";;

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

let view_inj = injectivity "view";;

export_thm view_inj;;

(* ------------------------------------------------------------------------- *)
(* Actions.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Output.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* System security policy.                                                   *)
(* ------------------------------------------------------------------------- *)

(***
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
   MP_TAC (ISPEC `(a' : page_directory_data) x''` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (SPEC `a'' : page_directory_entry` page_directory_entry_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_page_directory_entry_def] THEN
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
      output a s' = output a t'`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [GSYM view_equiv_def] THEN
   MATCH_MP_TAC weak_step_consistency THEN
   EXISTS_TAC `s : state` THEN
   EXISTS_TAC `t : state` THEN
   EXISTS_TAC `a : action` THEN
   ASM_REWRITE_TAC []);;

export_thm output_consistency;;
***)
***)

logfile_end ();;
