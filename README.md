# Decomposition Diversity with Symmetric Data and Codata

This is the formalization of our language with support for symmetric data and codata types.
The repository consists of three parts

- The [Formalization](Formalization/) subdirectory contains the Coq formalization.
- The [Repl](Repl/) subdirectory contains a REPL for the language.
- The [IDE](ide/) subdirectory contains a browser-based IDE for the language.

The formalization subdirectory contains further instructions on how to build the Coq-files and extract Haskell code, and an explanation of the results.
Both the REPL and the IDE use code which is extracted from the Coq formalization, but it is not necessary to extract that code yourself, since pre-extracted Haskell files are included in the `Repl/extracted` directory.

## Using the Repl

If you want to use the REPL, follow the instructions in the [Repl](Repl/) subdirectory.

## Using the IDE

Using the browser-based IDE requires that you have `docker` and `docker-compose` installed on your computer.

### Building the docker images locally

You can build and start the IDE with:

```console
docker-compose build
docker-compose up
```

The IDE should then be available under `localhost:8080/decompositiondiversity`.

(Note: under MacOS it might be necessary to increase the amount of memory allocated to docker during the build stage. The default is 2GB.).

### Using prebuilt docker images from docker-hub

The `docker-compose-prebuilt.yml` file downloads the prebuilt images directly from docker-hub instead of building them locally.

```console
docker-compose --file ./docker-compose-prebuilt.yml up
```

The IDE should then be available under `localhost:8080/decompositiondiversity`.

### Using the startup script

Alternatively, you can start the IDE by running the `startup-ide.sh` script.
This script accepts a parameter which allows changing the port on which the IDE is reachable.
After running

```
./startup-ide.sh $PORT
```

the IDE will be available under `localhost:$PORT/decompositiondiversity`.

