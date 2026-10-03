importScripts('model.js');

self.onmessage = function (e) {
  const id = e.data.id;
  try {
    self.postMessage({ id: id, res: self.NexusModel.plan(e.data.cfg) });
  } catch (err) {
    self.postMessage({ id: id, error: String((err && err.message) || err) });
  }
};
