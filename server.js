const http = require("http");
const url = require("url");
const fs = require("fs");
const path = require("path");

var mimeTypes = {
  html: "text/html",
  jpeg: "image/jpeg",
  jpg: "image/jpeg",
  png: "image/png",
  svg: "image/svg+xml",
  js: "text/javascript",
  css: "text/css",
  treo: "text/treo",
};

http
  .createServer((request, response) => {
    response.setHeader("Access-Control-Allow-Origin", "http://localhost:3000");
    var pathname = url.parse(request.url).pathname;
    var filename;
    if (pathname === "/nuXmv/compact") {
      processPost(request, response, function () {
        console.log(request.post.content);
        fs.writeFileSync("./Reo2nuXmv/input.txt", request.post.content);

        const { exec } = require("child_process");
        exec("cd Reo2nuXmv && ./reo2nuXmv", (err, stdout, stderr) => {
          if (err) {
            console.log(err);
            response.writeHead(500, { "Content-Type": "text/plain" });
            response.write(err.message);
            response.end(err.message);
            return;
          }
          var filestream = fs.createReadStream("./Reo2nuXmv/nuxmv2.smv");
          response.writeHead(200, { "Content-Type": "text/plain" });
          filestream.pipe(response);
        });
      });
    } else {
      if (pathname === "/nuXmv/components") {
        processPost(request, response, function () {
          fs.writeFileSync("./Reo2nuXmv/input.txt", request.post.content);

          const { exec } = require("child_process");
          exec("cd Reo2nuXmv && ./reo2nuXmv", (err, stdout, stderr) => {
            if (err) {
              console.log(err);
              response.writeHead(500, { "Content-Type": "text/plain" });
              response.write(err.message);
              response.end(err.message);
              return;
            } else {
              var filestream = fs.createReadStream("./Reo2nuXmv/nuxmv.smv");
              response.writeHead(200, { "Content-Type": "text/plain" });
              filestream.pipe(response);
            }
          });
        });
      } else {
        if (pathname === "/coq/model") {
          processPost(request, response, function () {
            fs.writeFileSync("./CACoq/input.txt", request.post.content);
            const { exec } = require("child_process");
            exec("(cd CACoq && ./reo2CACoq)", (err, stdout, stderr) => {
              if (err) {
                console.log(err);
                response.writeHead(500, { "Content-Type": "text/plain" });
                response.write(err.message);
                response.end(err.message);
                return;
              } else {
                var filestream = fs.createReadStream("./CACoq/coqModel.v");
                response.writeHead(200, { "Content-Type": "text/plain" });
                filestream.pipe(response);
              }
            });
          });
        } else {
          if (pathname === "/haskell/model") {
            processPost(request, response, function () {
              fs.writeFileSync("./CACoq/input.txt", request.post.content);
              const { exec } = require("child_process");
              exec(
                "(cd CACoq && ./reo2CACoqHs && coqc CaMain.v && coqc coqModelHs.v)",
                (err, stdout, stderr) => {
                  if (err) {
                    console.log(err);
                    response.writeHead(569, { "Content-Type": "text/plain" });
                    response.write(err.message);
                    response.end(err.message);
                    return response;
                  } else {
                    var filestream = fs.createReadStream(
                      "./CACoq/haskellModel.hs"
                    );
                    response.writeHead(200, { "Content-Type": "text/plain" });
                    filestream.pipe(response);
                  }
                }
              );
            });
          } else {
            if (pathname === "/") {
              filename = "./public/index.html";
            } else filename = path.join("./public", pathname);
            try {
              fs.accessSync(filename, fs.F_OK);
              var fileStream = fs.createReadStream(filename);
              var mimeType = mimeTypes[path.extname(filename).split(".")[1]];
              response.writeHead(200, { "Content-Type": mimeType });
              fileStream.pipe(response);
            } catch (e) {
              console.log("File not exists: " + filename);
              response.writeHead(404, { "Content-Type": "text/plain" });
              response.write("404 Not Found\n");
              response.end();
              return;
            }
          }
        }
        return;
      }
    }
  })
  .listen(8081, "127.0.0.1");

console.log("Server running at http://127.0.0.1:8081/");

function processPost(request, response, callback) {
  var queryData = "";
  if (typeof callback !== "function") return null;

  if (request.method == "POST") {
    request.on("data", function (data) {
      queryData += data;
      if (queryData.length > 1e6) {
        queryData = "";
        response.writeHead(413, { "Content-Type": "text/plain" }).end();
        request.connection.destroy();
      }
    });

    request.on("end", function () {
      request.post = JSON.parse(queryData);
      callback();
    });
  } else {
    response.writeHead(405, { "Content-Type": "text/plain" });
    response.end();
  }
}
