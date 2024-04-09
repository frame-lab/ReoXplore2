# syntax=docker/dockerfile:1

# Use Debian base image instead of Node
FROM debian:latest

# Install Node.js, build-essential, coq, and supervisor
RUN apt-get update && apt-get install -y \
    curl \
    build-essential \
    coq \
    nodejs

# Set the working directory
WORKDIR /usr/src/app

# Copy package.json and package-lock.json
COPY package*.json ./ 
COPY makefile ./
COPY Reo2nuXmv ./
COPY CACoq ./
COPY reoxplore ./ 

# Install app dependencies
RUN make

# Bundle app source
COPY . .

# Copy supervisord configuration file

# Expose the port the app runs on
EXPOSE 3000

# Run supervisord
CMD ["node", "server.js"]