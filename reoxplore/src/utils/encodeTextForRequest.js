export default function encodeTextForRequest(data) {
  return new TextEncoder().encode(
    JSON.stringify({
      content: data,
    })
  );
}
