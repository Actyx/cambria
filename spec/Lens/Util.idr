module Lens.Util

import Data.List
import Data.Maybe
import Lens
import Lens.Uninhabited
import Map

%default total

public export
beq_prim : (v : PrimitiveValue) ->  v == v = True
beq_prim (Boolean b) = beq_bool b
beq_prim (Number n) = beq_nat n
beq_prim (Text t) = beq_str t

public export
beq_prim2 : (v1, v2 : PrimitiveValue) -> (v1 == v2 = True) -> v1 = v2
beq_prim2 (Boolean x) (Boolean y) prf = rewrite eq_bool x y prf in Refl
beq_prim2 (Boolean _) (Number _) Refl impossible
beq_prim2 (Boolean _) (Text _) Refl impossible
beq_prim2 (Number _) (Boolean _) Refl impossible
beq_prim2 (Number k) (Number j) prf = rewrite eq_nat k j prf in Refl
beq_prim2 (Number _) (Text _) Refl impossible
beq_prim2 (Text _) (Boolean _) Refl impossible
beq_prim2 (Text _) (Number _) Refl impossible
beq_prim2 (Text xs) (Text ys) prf = rewrite eq_str xs ys prf in Refl

public export
neq_prim : (v1, v2 : PrimitiveValue) -> (v1 == v2 = False) -> Not (v1 = v2)
neq_prim (Boolean x) (Boolean y) prf =
    neq_bool x y prf . justInjective . cong boolean
neq_prim (Boolean x) (Number k) prf = uninhabited
neq_prim (Boolean x) (Text xs) prf = uninhabited
neq_prim (Number k) (Boolean x) prf = uninhabited
neq_prim (Number k) (Number j) prf =
    neq_nat k j prf . justInjective . cong number
neq_prim (Number k) (Text xs) prf = uninhabited
neq_prim (Text xs) (Boolean x) prf = uninhabited
neq_prim (Text xs) (Number k) prf = uninhabited
neq_prim (Text xs) (Text ys) prf =
    neq_str xs ys prf . justInjective . cong text


beq_prim_kind : (k1, k2 : PrimitiveKind) -> (k1 == k2 = True) ->  k1 = k2
beq_prim_kind KBoolean KBoolean prf = Refl
beq_prim_kind KBoolean KNumber Refl impossible
beq_prim_kind KBoolean KText Refl impossible
beq_prim_kind KNumber KBoolean Refl impossible
beq_prim_kind KNumber KNumber prf = Refl
beq_prim_kind KNumber KText Refl impossible
beq_prim_kind KText KBoolean Refl impossible
beq_prim_kind KText KNumber Refl impossible
beq_prim_kind KText KText prf = Refl


public export
validate_properties_after_insert : (vm : Map Value) -> (sm : Map Schema) ->
    (k : Key) -> (v : Value) -> (s : Schema) -> validate s v = True ->
    validate_properties vm sm = True -> validate_properties (insert k v vm) (insert k s sm) = True

public export
validate_properties_after_remove : (vm : Map Value) -> (sm : Map Schema) -> (k : Key) ->
    validate_properties vm sm = True -> validate_properties (remove k vm) (remove k sm) = True

public export
invalid_property : (vm : Map Value) -> (sm : Map Schema) -> (k : Key) ->
    (v : Value) -> (s : Schema) -> get k vm = Just v -> get k sm = Just s -> validate s v = False ->
    validate_properties vm sm = False

public export
still_valid : (vm : Map Value) -> (sm : Map Schema) ->
    (k : Key) -> (kvm : Value) -> (ksm : Schema) ->
    get k vm = Just kvm -> get k sm = Just ksm ->
    validate_properties vm sm = True -> validate ksm kvm = True

public export
still_invalid : (vm : Map Value) -> (sm : Map Schema) ->
    (k : Key) ->  get k vm = Just kvm -> get k sm = Just ksm ->
    validate ksm kvm = False -> validate_properties vm sm = False


public export
flip_map_twice : (m : List (PrimitiveValue, PrimitiveValue)) -> flip_map (flip_map m) = m
flip_map_twice [] = Refl
flip_map_twice ((x, y) :: xs) = rewrite flip_map_twice xs in Refl

public export
flip_map_preserves_validity : (a, b : PrimitiveKind) -> (m : List (PrimitiveValue, PrimitiveValue)) ->
    validate_map a b m = True -> validate_map b a (flip_map m) = True
flip_map_preserves_validity a b [] prf = Refl
flip_map_preserves_validity a b ((x, y) :: xs) prf =
    let sprf = and_split (prim_kind_of x == a) (prim_kind_of y == b && Delay (validate_map a b xs)) prf
        sprf2 = and_split (prim_kind_of y == b) (validate_map a b xs) (snd sprf)
        ind = flip_map_preserves_validity a b xs (snd sprf2)
    in rewrite fst sprf2 in rewrite fst sprf in ind

validate_map_kind_a : (m : List (PrimitiveValue, PrimitiveValue)) -> (a, b : PrimitiveKind) -> (va : PrimitiveValue) ->
    (va, vb) :: _ = m -> validate_map a b m = True -> prim_kind_of va = a
validate_map_kind_a [] _ _ _ Refl _ impossible
validate_map_kind_a ((va, vb) :: m) KBoolean b (Number _) prf prf1 =
    let split = and_split (prim_kind_of va == KBoolean) (prim_kind_of vb == b && validate_map KBoolean b m) prf1
        xeq = cong prim_kind_of $ cong fst $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of va) KBoolean (fst split)
    in absurd $ trans xeq xeq2
validate_map_kind_a ((va, vb) :: m) KBoolean b (Text _) prf prf1 =
    let split = and_split (prim_kind_of va == KBoolean) (prim_kind_of vb == b && validate_map KBoolean b m) prf1
        xeq = cong prim_kind_of $ cong fst $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of va) KBoolean (fst split)
    in absurd $ trans xeq xeq2
validate_map_kind_a ((va, vb) :: m) KNumber b (Boolean _) prf prf1 =
    let split = and_split (prim_kind_of va == KNumber) (prim_kind_of vb == b && validate_map KNumber b m) prf1
        xeq = cong prim_kind_of $ cong fst $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of va) KNumber (fst split)
    in absurd $ trans xeq xeq2
validate_map_kind_a ((va, vb) :: m) KNumber b (Text _) prf prf1 =
    let split = and_split (prim_kind_of va == KNumber) (prim_kind_of vb == b && validate_map KNumber b m) prf1
        xeq = cong prim_kind_of $ cong fst $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of va) KNumber (fst split)
    in absurd $ trans xeq xeq2
validate_map_kind_a ((va, vb) :: m) KText b (Boolean _) prf prf1 =
    let split = and_split (prim_kind_of va == KText) (prim_kind_of vb == b && validate_map KText b m) prf1
        xeq = cong prim_kind_of $ cong fst $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of va) KText (fst split)
    in absurd $ trans xeq xeq2
validate_map_kind_a ((va, vb) :: m) KText b (Number _) prf prf1 =
    let split = and_split (prim_kind_of va == KText) (prim_kind_of vb == b && validate_map KText b m) prf1
        xeq = cong prim_kind_of $ cong fst $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of va) KText (fst split)
    in absurd $ trans xeq xeq2
validate_map_kind_a ((_, _) :: _) KBoolean _ (Boolean _) prf prf1 = Refl
validate_map_kind_a ((_, _) :: _) KNumber _ (Number _) prf prf1 = Refl
validate_map_kind_a ((_, _) :: _) KText _ (Text _) prf prf1 = Refl

validate_map_kind_b : (m : List (PrimitiveValue, PrimitiveValue)) -> (a, b : PrimitiveKind) -> (vb : PrimitiveValue) ->
    (va, vb) :: _ = m -> validate_map a b m = True -> prim_kind_of vb = b
validate_map_kind_b [] _ _ _ Refl _ impossible
validate_map_kind_b ((va, vb) :: m) a KBoolean (Number _) prf prf1 =
    let split = and_split (prim_kind_of va == a) (prim_kind_of vb == KBoolean && validate_map a KBoolean m) prf1
        split2 = and_split (prim_kind_of vb == KBoolean) (validate_map a KBoolean m) (snd split)
        xeq = cong prim_kind_of $ cong snd $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of vb) KBoolean (fst split2)
    in absurd $ trans xeq xeq2
validate_map_kind_b ((va, vb) :: m) a KBoolean (Text _) prf prf1 =
    let split = and_split (prim_kind_of va == a) (prim_kind_of vb == KBoolean && validate_map a KBoolean m) prf1
        split2 = and_split (prim_kind_of vb == KBoolean) (validate_map a KBoolean m) (snd split)
        xeq = cong prim_kind_of $ cong snd $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of vb) KBoolean (fst split2)
    in absurd $ trans xeq xeq2
validate_map_kind_b ((va, vb) :: m) a KNumber (Boolean _) prf prf1 =
    let split = and_split (prim_kind_of va == a) (prim_kind_of vb == KNumber && validate_map a KNumber m) prf1
        split2 = and_split (prim_kind_of vb == KNumber) (validate_map a KNumber m) (snd split)
        xeq = cong prim_kind_of $ cong snd $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of vb) KNumber (fst split2)
    in absurd $ trans xeq xeq2
validate_map_kind_b ((va, vb) :: m) a KNumber (Text _) prf prf1 =
    let split = and_split (prim_kind_of va == a) (prim_kind_of vb == KNumber && validate_map a KNumber m) prf1
        split2 = and_split (prim_kind_of vb == KNumber) (validate_map a KNumber m) (snd split)
        xeq = cong prim_kind_of $ cong snd $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of vb) KNumber (fst split2)
    in absurd $ trans xeq xeq2
validate_map_kind_b ((va, vb) :: m) a KText (Boolean _) prf prf1 =
    let split = and_split (prim_kind_of va == a) (prim_kind_of vb == KText && validate_map a KText m) prf1
        split2 = and_split (prim_kind_of vb == KText) (validate_map a KText m) (snd split)
        xeq = cong prim_kind_of $ cong snd $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of vb) KText (fst split2)
    in absurd $ trans xeq xeq2
validate_map_kind_b ((va, vb) :: m) a KText (Number _) prf prf1 =
    let split = and_split (prim_kind_of va == a) (prim_kind_of vb == KText && validate_map a KText m) prf1
        split2 = and_split (prim_kind_of vb == KText) (validate_map a KText m) (snd split)
        xeq = cong prim_kind_of $ cong snd $ fst $ consInjective prf
        xeq2 = beq_prim_kind (prim_kind_of vb) KText (fst split2)
    in absurd $ trans xeq xeq2
validate_map_kind_b ((va, vb) :: m) _ KBoolean (Boolean _) prf prf1 = Refl
validate_map_kind_b ((va, vb) :: m) _ KNumber (Number _) prf prf1 = Refl
validate_map_kind_b ((va, vb) :: m) _ KText (Text _) prf prf1 = Refl


validate_map_kind : (m : List (PrimitiveValue, PrimitiveValue)) -> (a, b : PrimitiveKind) ->
    (va, vb : PrimitiveValue) -> (va, vb) :: _ = m -> validate_map a b m = True ->
    (prim_kind_of va = a, prim_kind_of vb = b)
validate_map_kind m a b va vb prf prf1 =
    let pa = validate_map_kind_a m a b va prf prf1
        pb = validate_map_kind_b m a b vb prf prf1
    in (pa, pb)

map_still_valid : (m : List (PrimitiveValue, PrimitiveValue)) -> (a, b : PrimitiveKind) ->
    (x :: xs) = m -> validate_map a b m = True -> validate_map a b xs = True
map_still_valid [] _ _ Refl _ impossible
map_still_valid ((va, vb) :: m) a b prf prf1 with (prim_kind_of va == a, prim_kind_of vb == b) proof prf2
    map_still_valid ((va, vb) :: m) a b prf prf1 | (False, _) =
        let split = and_split (prim_kind_of va == a) (prim_kind_of vb == b && validate_map a b m) prf1
        in absurd $ trans (sym $ cong fst prf2) (fst split)
    map_still_valid ((va, vb) :: m) a b prf prf1 | (True, False) =
        let split = and_split (prim_kind_of va == a) (prim_kind_of vb == b && validate_map a b m) prf1
            split2 = and_split (prim_kind_of vb == b) (validate_map a b m) (snd split)
        in absurd $ trans (sym $ cong snd prf2) (fst split2)
    map_still_valid ((va, vb) :: m) a b prf prf1 | (True, True) =
        let split = and_split (prim_kind_of va == a) (prim_kind_of vb == b && validate_map a b m) prf1
            split2 = and_split (prim_kind_of vb == b) (validate_map a b m) (snd split)
        in rewrite snd $ consInjective prf in snd split2

public export
convert_prim_kind : (m : List (PrimitiveValue, PrimitiveValue)) ->
    (a, b : PrimitiveKind) -> (va, vb : PrimitiveValue) ->
    validate_map a b m = True -> prim_kind_of va = a ->
    convert_prim va m = Just vb -> prim_kind_of vb = b
convert_prim_kind [] _ _ _ _ _ _ Refl impossible
convert_prim_kind ((va', vb') :: m) a b va vb prf prf1 prf2 with (va == va') proof prf3
    convert_prim_kind ((va', vb') :: m) a b va vb prf prf1 prf2 | True =
        rewrite sym $ justInjective prf2 in
            snd $ validate_map_kind ((va', vb') :: m) a b va' vb' Refl prf
    convert_prim_kind ((va', vb') :: m) a b va vb prf prf1 prf2 | False =
        let sv = map_still_valid ((va', vb') :: m) a b Refl prf
            ind = convert_prim_kind m a b va vb sv prf1 prf2
        in ind
