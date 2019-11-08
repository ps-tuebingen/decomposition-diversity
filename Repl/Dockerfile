# See: https://www.fpcomplete.com/blog/2017/12/building-haskell-apps-with-docker
# See: https://medium.com/permutive/optimized-docker-builds-for-haskell-76a9808eb10b

# ----------------------------------------------------------------------------------
# Building Dependencies

FROM fpco/stack-build:lts-13.22 as dependencies

RUN mkdir /opt/build
WORKDIR /opt/build

RUN apt-get update \
  && apt-get download libgmp10
RUN mv libgmp*.deb libgmp.deb

COPY stack.yaml package.yaml  /opt/build/
RUN stack build --system-ghc --dependencies-only

# ----------------------------------------------------------------------------------
# Building the project

FROM fpco/stack-build:lts-13.22 as build

COPY --from=dependencies /root/.stack /root/.stack
COPY . /opt/build/

WORKDIR /opt/build

RUN stack build --system-ghc

RUN mv "$(stack path --local-install-root --system-ghc)/bin" /opt/build/bin

# ----------------------------------------------------------------------------------
# Running the project

FROM ubuntu:16.04 as app

RUN mkdir -p /opt/decompositiondiversity/

WORKDIR /opt/decompositiondiversity

COPY --from=dependencies /opt/build/libgmp.deb /tmp
RUN dpkg -i /tmp/libgmp.deb && rm /tmp/libgmp.deb

COPY --from=build /opt/build/bin .

EXPOSE 9999

CMD ["/opt/decompositiondiversity/bin/Repl", "--json"]

