# Start with a base image that has Node.js installed
FROM node:14

# Install necessary dependencies
RUN apt-get update && apt-get install -y \
    git \
    build-essential \
    coq

# Set the working directory
WORKDIR /app

# Clone the repository
RUN git clone https://github.com/frame-lab/ReoXplore2 .

# Compile files and install packages
RUN make

# Expose the port the app runs on
EXPOSE 3000

# Set the command to run the server
CMD ["node", "server.js"]