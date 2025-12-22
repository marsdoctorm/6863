package org.lbee.network;

import org.lbee.protocol.Message;

/**
 * Message box interface for different delivery strategies
 */
public interface MessageBox {

    void put(Message message);

    Message take();
}
