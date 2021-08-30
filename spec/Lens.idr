module Lens

import Data.List
import Data.Maybe
import Map

%default total

data PrimitiveValue =
      Boolean Bool
    | Number Nat
    | Text (List Char)

%name PrimitiveValue val, v, v1, v2

Eq PrimitiveValue where
    Boolean b1 == Boolean b2 = b1 == b2
    Number n1 == Number n2 = n1 == n2
    Text t1 == Text t2 = t1 == t2
    _ == _ = False

boolean : (v : PrimitiveValue) -> Maybe Bool
boolean (Boolean b) = Just b
boolean _ = Nothing

number : (v : PrimitiveValue) -> Maybe Nat
number (Number n) = Just n
number _ = Nothing

text : (v : PrimitiveValue) -> Maybe (List Char)
text (Text t) = Just t
text _ = Nothing


data PrimitiveKind =
      KBoolean
    | KNumber
    | KText

%name PrimitiveKind k, k1, k2

Eq PrimitiveKind where
    KBoolean == KBoolean = True
    KNumber == KNumber = True
    KText == KText = True
    _ == _ = False

prim_kind_of : PrimitiveValue -> PrimitiveKind
prim_kind_of (Boolean x) = KBoolean
prim_kind_of (Number x) = KNumber
prim_kind_of (Text x) = KText


data Value =
      Null
    | Primitive PrimitiveValue
    | Array (List Value)
    | Object (Map Value)

%name Value val, v, v1, v2

Eq Value where
    Null == Null = True
    Primitive v1 == Primitive v2 = v1 == v2
    Array vs1 == Array vs2 = assert_total (vs1 == vs2)
    Object ps1 == Object ps2 = assert_total (ps1 == ps2)
    _ == _ = False

prim : Value -> Maybe PrimitiveValue
prim (Primitive v) = Just v
prim _ = Nothing

array : Value -> Maybe (List Value)
array (Array xs) = Just xs
array _ = Nothing

object : Value -> Maybe (Map Value)
object (Object m) = Just m
object _ = Nothing


data Kind =
      KNull
    | KPrimitive PrimitiveKind
    | KArray
    | KObject

%name Kind k, k1, k2

Eq Kind where
    KNull == KNull = True
    KPrimitive k1 == KPrimitive k2 = k1 == k2
    KArray == KArray = True
    KObject == KObject = True
    _ == _ = False


data Schema =
      SNull
    | SBoolean
    | SNumber
    | SText
    | SArray Bool Schema
    | SObject (Map Schema)

%name Schema s, s1, s2

allow_empty : Schema -> Maybe Bool
allow_empty (SArray e _) = Just e
allow_empty _ = Nothing

sarray : Schema -> Maybe Schema
sarray (SArray _ s) = Just s
sarray _ = Nothing

mutual
    validate_properties' : List Key -> Map Value -> Map Schema -> Bool
    validate_properties' [] _ _ = True
    validate_properties' (k :: ks) vm sm with (get k vm, get k sm)
        validate_properties' (k :: ks) vm sm | (Just v, Just s) =
             assert_total (validate s v) && validate_properties' ks vm sm
        validate_properties' (k :: ks) vm sm | (_, _) = False

    validate_properties : Map Value -> Map Schema -> Bool
    validate_properties vm sm = validate_properties' (keys vm) vm sm

    validate : Schema -> Value -> Bool
    validate SNull Null = True
    validate SNull _ = False
    validate SBoolean (Primitive (Boolean _)) = True
    validate SBoolean _ = False
    validate SNumber (Primitive (Number _)) = True
    validate SNumber _ = False
    validate SText (Primitive (Text _)) = True
    validate SText _ = False
    validate (SArray e _) (Array []) = e
    validate (SArray _ s) (Array (x :: xs)) =
        assert_total (validate s) x && assert_total (validate (SArray True s) (Array xs))
    validate (SArray _ _) _ = False
    validate (SObject sm) (Object vm) =
        half_keys_eq sm vm && validate_properties vm sm
    validate (SObject _) _ = False


data Lens =
      Make Kind
    | Destroy Kind
    | AddProperty Key
    | RemoveProperty Key
    | RenameProperty Key Key
    | HoistProperty Key Key
    | PlungeProperty Key Key
    | Wrap
    | Head
    | LensIn Key Lens
    | LensMap Lens
    | Convert PrimitiveKind PrimitiveKind (List (PrimitiveValue, PrimitiveValue))

%name Lens lens, l, l1, l2

Eq Lens where
    Make k1 == Make k2 = k1 == k2
    Destroy k1 == Destroy k2 = k1 == k2
    AddProperty p1 == AddProperty p2 = p1 == p2
    RemoveProperty p1 == RemoveProperty p2 = p1 == p2
    RenameProperty a1 b1 == RenameProperty a2 b2 = a1 == a2 && b1 == b2
    HoistProperty h1 p1 == HoistProperty h2 p2 = h1 == h2 && p1 == p2
    PlungeProperty h1 p1 == PlungeProperty h2 p2 = h1 == h2 && p1 == p2
    Wrap == Wrap = True
    Head == Head = True
    LensIn p1 l1 == LensIn p2 l2 = p1 == p2 && l1 == l2
    LensMap l1 == LensMap l2 = l1 == l2
    Convert k11 k21 f1 == Convert k12 k22 f2 = k11 == k12 && k22 == k22 && f1 == f2
    _ == _ = False


flip_map : List (PrimitiveValue, PrimitiveValue) -> List (PrimitiveValue, PrimitiveValue)
flip_map [] = []
flip_map ((x, y) :: xs) = (y, x) :: (flip_map xs)

validate_map : PrimitiveKind -> PrimitiveKind -> List (PrimitiveValue, PrimitiveValue) -> Bool
validate_map _ _ [] = True
validate_map kx ky ((x, y) :: map) =
    prim_kind_of x == kx && prim_kind_of y == ky && validate_map kx ky map

convert_prim : PrimitiveValue -> List (PrimitiveValue, PrimitiveValue) -> Maybe PrimitiveValue
convert_prim _ [] = Nothing
convert_prim key ((k, v) :: xs) = if key == k then Just v else convert_prim key xs


reverse_lens : Lens -> Lens
reverse_lens (Make k) = Destroy k
reverse_lens (Destroy k) = Make k
reverse_lens (AddProperty x) = RemoveProperty x
reverse_lens (RemoveProperty x) = AddProperty x
reverse_lens (RenameProperty x y) = RenameProperty y x
reverse_lens (HoistProperty x y) = PlungeProperty x y
reverse_lens (PlungeProperty x y) = HoistProperty x y
reverse_lens Wrap = Head
reverse_lens Head = Wrap
reverse_lens (LensIn x y) = LensIn x (reverse_lens y)
reverse_lens (LensMap x) = LensMap (reverse_lens x)
reverse_lens (Convert a b m) = Convert b a (flip_map m)

strip_postfix : Eq a => List a -> List a -> (List a, List a)
strip_postfix (a::as) (b::bs) =
    if a == b
    then strip_postfix as bs
    else (a::as, b::bs)
strip_postfix a b = (a, b)

transform_lenses : List Lens -> List Lens -> List Lens
transform_lenses a b =
    let
        a = reverse a
        b = reverse b
        (a, b) = strip_postfix a b
        a = reverse a
        a = map reverse_lens a
    in a ++ b

transform_schema : Lens -> Schema -> Maybe Schema
transform_schema (Make (KPrimitive KBoolean)) SNull = Just SBoolean
transform_schema (Make (KPrimitive KNumber)) SNull = Just SNumber
transform_schema (Make (KPrimitive KText)) SNull = Just SText
transform_schema (Make KArray) SNull = Just (SArray True SNull)
transform_schema (Make KObject) SNull = Just (SObject Empty)
transform_schema (Make _) _ = Nothing
transform_schema (Destroy (KPrimitive KBoolean)) SBoolean = Just SNull
transform_schema (Destroy (KPrimitive KNumber)) SNumber = Just SNull
transform_schema (Destroy (KPrimitive KText)) SText = Just SNull
transform_schema (Destroy KArray) (SArray True SNull) = Just SNull
transform_schema (Destroy KObject) (SObject Empty) = Just SNull
transform_schema (Destroy KObject) (SObject _) = Nothing
transform_schema (Destroy _) _ = Nothing
transform_schema (AddProperty key) (SObject smap) =
    case get key smap of
        Just _ => Nothing
        Nothing => Just (SObject (insert key SNull smap))
transform_schema (AddProperty _) _ = Nothing
transform_schema (RemoveProperty key) (SObject smap) =
    case get key smap of
        Just SNull => Just (SObject (remove key smap))
        _ => Nothing
transform_schema (RemoveProperty _) _ = Nothing
transform_schema (RenameProperty x y) (SObject smap) =
    case (get x smap, get y smap) of
        (Just p, Nothing) =>
            let
                smap = (remove x smap)
                smap = (insert y p smap)
            in Just (SObject smap)
        _ => Nothing
transform_schema (RenameProperty _ _) _ = Nothing
transform_schema (HoistProperty h t) (SObject m) =
    case (get h m, get t m) of
        (Just (SObject hm), Nothing) =>
            case get t hm of
                Just p =>
                    let
                        hm = remove t hm
                        m = insert t p m
                        m = insert h (SObject hm) m
                     in Just (SObject m)
                Nothing => Nothing
        _ => Nothing
transform_schema (HoistProperty _ _) _ = Nothing
transform_schema (PlungeProperty h t) (SObject m) =
    case (get t m, get h m, t == h) of
        (Just p, Just (SObject hm), False) =>
            case get t hm of
                Nothing =>
                    let
                        hm = insert t p hm
                        m = remove t m
                        m = insert h (SObject hm) m
                    in Just (SObject m)
                _ => Nothing
        _ => Nothing
transform_schema (PlungeProperty _ _) _ = Nothing
transform_schema Wrap schema = Just (SArray False schema)
transform_schema Head (SArray False schema) = Just schema
transform_schema Head _ = Nothing
transform_schema (LensIn key lens) (SObject smap) =
    case get key smap of
        Just schema =>
            case transform_schema lens schema of
                Just schema => Just (SObject (insert key schema smap))
                Nothing => Nothing
        Nothing => Nothing
transform_schema (LensIn _ _) _ = Nothing
transform_schema (LensMap lens) (SArray allowEmpty schema) =
    case transform_schema lens schema of
        Just schema' => Just (SArray allowEmpty schema')
        Nothing => Nothing
transform_schema (LensMap _) _ = Nothing
transform_schema (Convert a b map) s with (validate_map a b map)
    transform_schema (Convert KBoolean KBoolean _) SBoolean | True = Just SBoolean
    transform_schema (Convert KBoolean KNumber _) SBoolean | True = Just SNumber
    transform_schema (Convert KBoolean KText _) SBoolean | True = Just SText
    transform_schema (Convert KNumber KBoolean _) SNumber | True = Just SBoolean
    transform_schema (Convert KNumber KNumber _) SNumber | True = Just SNumber
    transform_schema (Convert KNumber KText _) SNumber | True = Just SText
    transform_schema (Convert KText KBoolean _) SText | True = Just SBoolean
    transform_schema (Convert KText KNumber _) SText | True = Just SNumber
    transform_schema (Convert KText KText _) SText | True = Just SText
    transform_schema (Convert _ _ _) _ | _ = Nothing

lenses_to_schema : List Lens -> Maybe Schema
lenses_to_schema [] = Just SNull
lenses_to_schema (l::ls) =
    case lenses_to_schema ls of
        Just s => transform_schema l s
        Nothing => Nothing

transform_value : Lens -> Value -> Value
transform_value (Make KNull) _ = Null
transform_value (Make (KPrimitive KBoolean)) _ = Primitive (Boolean False)
transform_value (Make (KPrimitive KNumber)) _ = Primitive (Number 0)
transform_value (Make (KPrimitive KText)) _ = Primitive (Text [])
transform_value (Make KArray) _ = Array []
transform_value (Make KObject) _ = Object Empty
transform_value (Destroy _) _ = Null
transform_value (AddProperty k) (Object m) = Object (insert k Null m)
transform_value (AddProperty _) v = v
transform_value (RemoveProperty k) (Object m) = Object (remove k m)
transform_value (RemoveProperty _) v = v
transform_value (RenameProperty k1 k2) (Object m) =
    case get k1 m of
        Just v => Object (insert k2 v (remove k1 m))
        Nothing => Object m
transform_value (RenameProperty _ _) v = v
transform_value (HoistProperty h t) (Object m) =
    case get h m of
        Just (Object hm) =>
            case get t hm of
                Just v => Object (insert h (Object (remove t hm)) $ insert t v m)
                Nothing => Object m
        _ => Object m
transform_value (HoistProperty _ _) v = v
transform_value (PlungeProperty h t) (Object m) =
    case (get h m, get t m) of
        (Just (Object hm), Just v) => Object (insert h (Object (insert t v hm)) $ remove t m)
        _ => Object m
transform_value (PlungeProperty _ _) v = v
transform_value Wrap v = Array [v]
transform_value Head (Array (x :: _)) = x
transform_value Head v = v
transform_value (LensIn k l) (Object vm) =
    case get k vm of
        Just v => Object (insert k (transform_value l v) vm)
        Nothing => Object vm
transform_value (LensIn _ _) v = v
transform_value (LensMap l) (Array xs) = Array (map (transform_value l) xs)
transform_value (LensMap _) v = v
transform_value (Convert _ b m) (Primitive v) =
    case convert_prim v m of
        Just v => (Primitive v)
        Nothing => case b of
            KBoolean => Primitive (Boolean False)
            KNumber => Primitive (Number 0)
            KText => Primitive (Text [])
transform_value (Convert _ _ _) v = v
