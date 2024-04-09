# Use Node.js base image
FROM node:latest

# Install build-essential and coq
RUN apt-get update && apt-get install -y \
    curl \
    build-essential \
    coq

# Set the working directory
WORKDIR /usr/src/app

# Copy package.json and package-lock.json
COPY package*.json ./ 
COPY src ./
COPY public ./

# Install app dependencies
RUN npm install

# Bundle app source
COPY . .

# Expose the port the app runs on
EXPOSE 8081

# Start the application
CMD ["npm", "start"]