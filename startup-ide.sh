#!/usr/bin/env sh
if [ -z "$1" ]; then
    HOST_PORT="8080"
else
    HOST_PORT="$1"
fi
HOST_PORT=$HOST_PORT docker-compose up
