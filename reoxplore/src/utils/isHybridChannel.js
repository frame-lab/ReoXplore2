export default function isHybridChannel(channel) {
  if (channel === "timer") return true;
  if (channel === "timeddelay") return true;
  if (channel === "timedtransform") return true;

  return false;
}
