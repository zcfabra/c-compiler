# Use an x86 Ubuntu base image
FROM --platform=linux/amd64 ubuntu:20.04

# Install necessary tools
RUN apt-get update && apt-get install -y \
    build-essential \
    gcc \
    nano \
    python3 \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Set the working directory
WORKDIR /app



