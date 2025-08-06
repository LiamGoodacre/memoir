## Haskell records via ImplicitParams

(experiment, not actually a library yet (or possibly ever))

### Anonymous record types, construction, dot notation

```hs
type Dog =
  '[ ?name :: String,
     ?goodboy :: Bool
   ]

dog :: Memoir Dog
dog = do
  let ?name = "Bongo"
  let ?goodboy = True
  MkMemoir

main = putStrLn $ "Dog's name: " ++ dog.name
```

### Interop with data records

```hs
data DogData = MkDogData
  { name :: String,
    goodboy :: Bool
  }

dogToDogData :: Memoir Dog -> DogData
dogToDogData = memoirToData

dogDataToDog :: DogData -> Memoir Dog
dogDataToDog = dataToMemoir
```

### Miscellaneous

* Semigroup & Monoid instances
* sequenceMemoir
* recollect
* memoirOfEmpty

```hs
example :: Maybe (Memoir '[?fieldA :: Int, ?fieldB :: Bool])
example = sequenceMemoir do
  let ?fieldA = Just 42
  let ?fieldB = Just True
  MkMemoir
```
