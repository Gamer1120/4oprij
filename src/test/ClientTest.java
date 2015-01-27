package test;

import java.io.IOException;
import java.net.InetAddress;

import client.Client;
import client.ClientTUI;

public class ClientTest {
	// HOW TO SETUP THIS TEST
	// 1. Launch ServerGUI on port 2727.
	// 2. Run a ClientTUI. Enter localhost for the IP, 2727 for the port and -N TestOpponent as name.
	// 3. Run this test.
	public static void main(String[] args) {
		Client cl = null;
		try {
			cl = new Client(InetAddress.getByName("localhost"), 2727, new ClientTUI());
		} catch (IOException e) {
			System.out.println("Couldn't create a client. Did you turn on the server?");
		}
		cl.setUpPlayer("ClientTest");
		System.out.println("The name of this Client should be ClientTest. It acutally is: " + cl.getClientName());
		cl.sendMessage(Client.CONNECT + " " + cl.getClientName());
		cl.sendMessage(Client.PING);
		cl.sendMessage(Client.PING);
		cl.sendMessage(Client.PING);
		System.out.println("On the console of the server, it should say that ClientTest has connected, sent 3 pings and left.");
	}

}
