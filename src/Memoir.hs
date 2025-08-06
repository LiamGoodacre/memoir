module Memoir where

import Data.Constraint (type (|-))
import Data.Kind (Constraint, Type)
import GHC.Classes (IP (ip))
import GHC.Generics qualified as Generics
import GHC.Magic.Dict (withDict)
import GHC.Records (HasField (..))
import GHC.TypeLits (Symbol)

type Each :: [Constraint] -> Constraint
type family Each cs = o | o -> cs where
  Each (h ': t) = (h, Each t)
  Each '[] = ()

data Memoir (cs :: [Constraint]) where
  MkMemoir :: (Each cs) => Memoir cs

recollect :: (Each i |- Each o) => Memoir i -> Memoir o
recollect MkMemoir = MkMemoir
{-# INLINE recollect #-}

type Lookup :: Symbol -> [Constraint] -> Maybe Type
type family Lookup field cs where
  Lookup field (IP field h ': t) = 'Just h
  Lookup field (IP other h ': t) = Lookup field t
  Lookup field '[] = 'Nothing

instance (Lookup field cs ~ 'Just i, Each cs |- IP field i) => HasField field (Memoir cs) i where
  getField MkMemoir = ip @field
  {-# INLINE getField #-}

type GFieldsOf :: (Type -> Type) -> [Constraint] -> [Constraint]
type family GFieldsOf rep e

type instance GFieldsOf (Generics.D1 m v) e = GFieldsOf v e

type instance GFieldsOf (Generics.C1 m v) e = GFieldsOf v e

type instance GFieldsOf (l Generics.:*: r) e = GFieldsOf l (GFieldsOf r e)

type instance
  GFieldsOf
    ( Generics.S1
        ('Generics.MetaSel ('Just field) _p _s _l)
        (Generics.Rec0 t)
    )
    e =
    IP field t ': e

type FieldsOf t = GFieldsOf (Generics.Rep t) '[]

class GDataToMemoir rep where
  gdataToMemoir :: Memoir o -> rep i -> Memoir (GFieldsOf rep o)

instance (GDataToMemoir v) => GDataToMemoir (Generics.D1 m v) where
  gdataToMemoir o (Generics.M1 v) = gdataToMemoir o v
  {-# INLINE gdataToMemoir #-}

instance (GDataToMemoir v) => GDataToMemoir (Generics.C1 m v) where
  gdataToMemoir o (Generics.M1 v) = gdataToMemoir o v
  {-# INLINE gdataToMemoir #-}

instance (GDataToMemoir l, GDataToMemoir r) => GDataToMemoir (l Generics.:*: r) where
  gdataToMemoir o (l Generics.:*: r) = gdataToMemoir (gdataToMemoir o r) l
  {-# INLINE gdataToMemoir #-}

instance GDataToMemoir (Generics.S1 ('Generics.MetaSel ('Just field) _p _s _l) (Generics.Rec0 t)) where
  gdataToMemoir MkMemoir (Generics.M1 (Generics.K1 v)) = withDict @(IP field t) v MkMemoir
  {-# INLINE gdataToMemoir #-}

dataToMemoir ::
  forall d.
  (Generics.Generic d, GDataToMemoir (Generics.Rep d)) =>
  d -> Memoir (FieldsOf d)
dataToMemoir = gdataToMemoir @(Generics.Rep d) (MkMemoir @'[]) . Generics.from @d
{-# INLINE dataToMemoir #-}

class GMemoirToData cs rep where
  gmemoirToData :: Memoir cs -> rep i

instance (GMemoirToData cs v) => GMemoirToData cs (Generics.D1 m v) where
  gmemoirToData d = Generics.M1 (gmemoirToData @cs @v d)
  {-# INLINE gmemoirToData #-}

instance (GMemoirToData cs v) => GMemoirToData cs (Generics.C1 m v) where
  gmemoirToData d = Generics.M1 (gmemoirToData @cs @v d)
  {-# INLINE gmemoirToData #-}

instance (GMemoirToData cs l, GMemoirToData cs r) => GMemoirToData cs (l Generics.:*: r) where
  gmemoirToData d = gmemoirToData @cs @l d Generics.:*: gmemoirToData @cs @r d
  {-# INLINE gmemoirToData #-}

instance
  (Each cs |- IP field t) =>
  GMemoirToData cs (Generics.S1 ('Generics.MetaSel ('Just field) _p _s _l) (Generics.Rec0 t))
  where
  gmemoirToData MkMemoir = Generics.M1 (Generics.K1 (ip @field))
  {-# INLINE gmemoirToData #-}

memoirToData ::
  forall r.
  ( Generics.Generic r,
    GMemoirToData (FieldsOf r) (Generics.Rep r)
  ) =>
  Memoir (FieldsOf r) -> r
memoirToData d = Generics.to @r (gmemoirToData @(FieldsOf r) @(Generics.Rep r) d)
{-# INLINE memoirToData #-}

type MapFields :: (Type -> Type) -> [Constraint] -> [Constraint]
type family MapFields f cs where
  MapFields f (IP field t ': r) = IP field (f t) ': MapFields f r
  MapFields f '[] = '[]

class SequenceMemoir (cs :: [Constraint]) where
  sequenceMemoir :: (Applicative f) => Memoir (MapFields f cs) -> f (Memoir cs)

instance SequenceMemoir '[] where
  sequenceMemoir _ = pure MkMemoir
  {-# INLINE sequenceMemoir #-}

instance (SequenceMemoir cs) => SequenceMemoir (IP field t ': cs) where
  sequenceMemoir MkMemoir =
    liftA2
      (\v MkMemoir -> withDict @(IP field t) v MkMemoir)
      (ip @field)
      (sequenceMemoir @cs MkMemoir)
  {-# INLINE sequenceMemoir #-}

type Every :: (Type -> Constraint) -> [Constraint] -> Constraint
type family Every p cs where
  Every p (IP field h ': t) = (p h, Every p t)
  Every p '[] = ()

instance Semigroup (Memoir '[]) where
  _ <> _ = MkMemoir
  {-# INLINE (<>) #-}

instance (Semigroup h, Semigroup (Memoir t)) => Semigroup (Memoir (IP field h ': t)) where
  l <> r = do
    let lh = case l of MkMemoir -> ip @field @h
    let rh = case r of MkMemoir -> ip @field @h
    withDict @(IP field h) (lh <> rh) do
      let lt = case l of MkMemoir -> MkMemoir @t
      let rt = case l of MkMemoir -> MkMemoir @t
      case lt <> rt of MkMemoir -> MkMemoir
  {-# INLINE (<>) #-}

instance Monoid (Memoir '[]) where
  mempty = MkMemoir
  {-# INLINE mempty #-}

instance (h ~ IP field x, Monoid x, Monoid (Memoir t)) => Monoid (Memoir (h ': t)) where
  mempty = withDict @(IP field x) mempty case mempty @(Memoir t) of MkMemoir -> MkMemoir
  {-# INLINE mempty #-}

class PointMemoir cs where
  memoirOfEmpty :: forall f. (forall i. f i) -> Memoir (MapFields f cs)

instance PointMemoir '[] where
  memoirOfEmpty _ = MkMemoir
  {-# INLINE memoirOfEmpty #-}

instance (h ~ IP field x, PointMemoir t) => PointMemoir (h ': t) where
  memoirOfEmpty @f f = withDict @(IP field (f x)) f case memoirOfEmpty @t f of MkMemoir -> MkMemoir
  {-# INLINE memoirOfEmpty #-}

---

type PersonFields =
  '[ ?fieldA :: Int,
     ?fieldB :: Bool
   ]

person0 :: Memoir PersonFields
person0 = do
  let ?fieldA = 42
  let ?fieldB = True
  MkMemoir

data Person = MkPerson {fieldA :: Int, fieldB :: Bool}
  deriving stock (Generics.Generic)

person1 :: Memoir (FieldsOf Person)
person1 = person0

person2 :: Memoir (FieldsOf Person)
person2 = dataToMemoir MkPerson {fieldA = 42, fieldB = True}

person3 :: Person
person3 = memoirToData person2

personMaybe :: Memoir (MapFields Maybe PersonFields)
personMaybe = do
  let ?fieldA = Just 42
  let ?fieldB = Just True
  MkMemoir

maybePerson :: Maybe (Memoir PersonFields)
maybePerson = sequenceMemoir personMaybe

maybePerson2 :: Maybe Person
maybePerson2 = memoirToData <$> maybePerson

egUse :: Memoir PersonFields -> String
egUse person =
  "Hello " <> show person.fieldA

type Bongo = MapFields [] (FieldsOf Person)

bongo :: Memoir Bongo -> Memoir Bongo -> Memoir Bongo
bongo = (<>)

example :: Maybe (Memoir '[?fieldA :: Int, ?fieldB :: Bool])
example = sequenceMemoir do
  let ?fieldA = Just 42
  let ?fieldB = Just True
  MkMemoir
