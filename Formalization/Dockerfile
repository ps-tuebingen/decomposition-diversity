# Building the Coq project and extracting the Haskell sources.
FROM coqorg/coq:8.8.2

# Copy all necessary files into the container
COPY *.v                ./
COPY Makefile           .
COPY prepend-imports.sh .

# Append the coq binaries to the path variable
ENV PATH=$PATH:/home/coq/.opam/4.05.0/bin/

# Build the Coq project
RUN ["make", "-j", "4", "all"]

# Extract the Haskell files
RUN ["make", "extract"]
