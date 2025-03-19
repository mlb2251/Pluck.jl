#!/bin/bash

# This script monitors the memory usage of a process
# Usage: ./monitor_process.sh <PID>

# Check if a PID was provided
if [ $# -eq 0 ]; then
    echo "Usage: $0 <PID>"
    exit 1
fi

PID=$1

echo "Monitoring process $PID"
echo "Time RSS_MB"

# Monitor the process until it exits
while kill -0 $PID 2>/dev/null; do
    # Get memory usage (RSS and VSZ)
    if [[ "$OSTYPE" == "darwin"* ]]; then
        # macOS
        MEM_INFO=$(ps -o rss= -p $PID)
        RSS=$(echo $MEM_INFO | awk '{print $1}')
    else
        # Linux
        MEM_INFO=$(ps -o rss= -p $PID)
        RSS=$(echo $MEM_INFO | awk '{print $1}')
    fi
    
    # Convert to MB
    RSS_MB=$(echo "scale=2; $RSS/1024" | bc)
    
    # Print with timestamp
    echo "$(date +%H:%M:%S) $RSS_MB MB"
    
    # Wait before checking again
    sleep 10
done

echo "Process $PID has exited"