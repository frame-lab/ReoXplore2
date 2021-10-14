const http = require("http");

const options = {
  hostname: "localhost",
  port: 8081,
  method: "POST",
};

async function makeRequest(data, path) {
  options["path"] = path;
  return await new Promise((resolve, reject) => {
    const req = http.request(options, (res) => {
      console.log(`statusCode: ${res.statusCode}`);

      res.on("data", (d) => {
        const dataString = new TextDecoder().decode(d);
        resolve({ status: res.statusCode, data: dataString });
      });
    });

    req.on("error", (error) => {
      console.error(error);
      reject(error);
    });

    req.write(data);
    req.end();
  });
}

export default makeRequest;
