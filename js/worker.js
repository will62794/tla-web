// TODO: Just a skeleton here.

console.log("Worker is running...")

onmessage = (e) => {
    console.log("Message received from main script");
    const workerResult = `Result: ${e.data}`;
    console.log(e.data);
    console.log("Posting message back to main script");
    postMessage(workerResult);
};