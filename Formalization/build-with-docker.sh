#!/bin/sh

# Build the image
docker build \
       --tag decomposition-diversity \
       --file Dockerfile \
       .

# Run a container in order to get to the extracted Haskell files.
docker run \
       --detach \
       --name decomposition-diversity-container \
       decomposition-diversity

docker cp decomposition-diversity-container:/home/coq/haskell .
docker stop decomposition-diversity-container
docker rm decomposition-diversity-container
