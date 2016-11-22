/*
 *
 * Copyright 2015, Google Inc.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above
 * copyright notice, this list of conditions and the following disclaimer
 * in the documentation AN/or other materials provided with the
 * distribution.
 *     * Neither the name of Google Inc. nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include <map>
#include <cctype>
#include <sstream>

#include "src/compiler/go_generator.h"

template <class T>
grpc::string as_string(T x) {
	std::ostringstream out;
	out << x;
	return out.str();
}

namespace grpc_go_generator {

// Returns string with first letter to lowerCase
grpc::string unexportName(grpc::string s) {
	if (s.size() <= 0)
		return s;
	s[0] = std::tolower(s[0]);
	return s;
}

// Returns string with first letter to uppercase
grpc::string exportName(grpc::string s) {
	if (s.size() <= 0)
		return s;
	s[0] = std::toupper(s[0]);
	return s;
}

// Generates imports for the service
void GenerateImports(grpc_generator::File *file, grpc_generator::Printer *printer,
                     std::map<grpc::string, grpc::string> vars) {
	vars["filename"] = file->filename();
	printer->Print("//Generated by gRPC Go plugin \n");
	printer->Print("//If you make any local changes, they will be lost\n");
	printer->Print(vars, "//source: $filename$\n\n");
	printer->Print(vars, "package $Package$\n\n");
	if (file->additional_imports() != "") {
		printer->Print(file->additional_imports().c_str());
		printer->Print("\n\n");
	}
	printer->Print("import (\n");
	printer->Indent();
	printer->Print(vars, "$context$ \"golang.org/x/net/context\"\n");
	printer->Print(vars, "$grpc$ \"google.golang.org/grpc\"\n");
	printer->Outdent();
	printer->Print(")\n\n");
}

// Generates Server method signature source
void GenerateServerMethodSignature(const grpc_generator::Method *method, grpc_generator::Printer *printer,
                                   std::map<grpc::string, grpc::string> vars) {
	vars["Method"] = exportName(method->name());
	vars["Request"] = method->input_name();
	vars["Response"] = (vars["CustomMethodIO"] == "") ? method->output_name() : vars["CustomMethodIO"];
	if (method->NoStreaming()) {
		printer->Print(vars, "$Method$($context$.Context, *$Request$) (*$Response$, error)");
	} else if (method->ServerOnlyStreaming()) {
		printer->Print(vars, "$Method$(*$Request$, $Service$_$Method$Server) error");
	} else {
		printer->Print(vars, "$Method$($Service$_$Method$Server) error");
	}
}

void GenerateServerMethod(const grpc_generator::Method *method, grpc_generator::Printer *printer,
                          std::map<grpc::string, grpc::string> vars) {
	vars["Method"] = exportName(method->name());
	vars["Request"] = method->input_name();
	vars["Response"] = (vars["CustomMethodIO"] == "") ? method->output_name() : vars["CustomMethodIO"];
	vars["FullMethodName"] = "/" + vars["Package"] + "." + vars["Service"] + "/" + vars["Method"];
	vars["Handler"] = "_" + vars["Service"] + "_" + vars["Method"] + "_Handler";
	if (method->NoStreaming()) {
		printer->Print(vars, "func $Handler$(srv interface{}, ctx $context$.Context,\n\tdec func(interface{}) error, interceptor $grpc$.UnaryServerInterceptor) (interface{}, error) {\n");
		printer->Indent();
		printer->Print(vars, "in := new($Request$)\n");
		printer->Print("if err := dec(in); err != nil { return nil, err }\n");
		printer->Print(vars, "if interceptor == nil { return srv.($Service$Server).$Method$(ctx, in) }\n");
		printer->Print(vars, "info := &$grpc$.UnaryServerInfo{\n");
		printer->Indent();
		printer->Print("Server: srv,\n");
		printer->Print(vars, "FullMethod: \"$FullMethodName$\",\n");
		printer->Outdent();
		printer->Print("}\n\n");
		printer->Print(vars, "handler := func(ctx $context$.Context, req interface{}) (interface{}, error) {\n");
		printer->Indent();
		printer->Print(vars, "return srv.($Service$Server).$Method$(ctx, req.(* $Request$))\n");
		printer->Outdent();
		printer->Print("}\n");
		printer->Print("return interceptor(ctx, in, info, handler)\n");
		printer->Outdent();
		printer->Print("}\n\n");
		return;
	}
	vars["StreamType"] = vars["ServiceUnexported"] + vars["Method"] + "Server";
	printer->Print(vars, "func $Handler$(srv interface{}, stream $grpc$.ServerStream) error {\n");
	printer->Indent();
	if (method->ServerOnlyStreaming()) {
		printer->Print(vars, "m := new($Request$)\n");
		printer->Print(vars, "if err := stream.RecvMsg(m); err != nil { return err }\n");
		printer->Print(vars, "return srv.($Service$Server).$Method$(m, &$StreamType${stream})\n");
	} else {
		printer->Print(vars, "return srv.($Service$Server).$Method$(&$StreamType${stream})\n");
	}
	printer->Outdent();
	printer->Print("}\n\n");

	bool genSend = method->BidiStreaming() || method->ServerOnlyStreaming();
	bool genRecv = method->BidiStreaming() || method->ClientOnlyStreaming();
	bool genSendAndClose = method->ClientOnlyStreaming();

	printer->Print(vars, "type $Service$_$Method$Server interface { \n");
	printer->Indent();
	if (genSend) {
		printer->Print(vars, "Send(* $Response$) error\n");
	}
	if (genRecv) {
		printer->Print(vars, "Recv() (* $Request$, error)\n");
	}
	if (genSendAndClose) {
		printer->Print(vars, "SendAndClose(* $Response$) error\n");
	}
	printer->Print(vars, "$grpc$.ServerStream\n");
	printer->Outdent();
	printer->Print("}\n\n");

	printer->Print(vars, "type $StreamType$ struct {\n");
	printer->Indent();
	printer->Print(vars, "$grpc$.ServerStream\n");
	printer->Outdent();
	printer->Print("}\n\n");

	if (genSend) {
		printer->Print(vars, "func (x *$StreamType$) Send(m *$Response$) error {\n");
		printer->Indent();
		printer->Print("return x.ServerStream.SendMsg(m)\n");
		printer->Outdent();
		printer->Print("}\n\n");
	}
	if (genRecv) {
		printer->Print(vars, "func (x *$StreamType$) Recv() (*$Request$, error) {\n");
		printer->Indent();
		printer->Print(vars, "m := new($Request$)\n");
		printer->Print("if err := x.ServerStream.RecvMsg(m); err != nil { return nil, err }\n");
		printer->Print("return m, nil\n");
		printer->Outdent();
		printer->Print("}\n\n");
	}
	if (genSendAndClose) {
		printer->Print(vars, "func (x *$StreamType$) SendAndClose(m *$Response$) error {\n");
		printer->Indent();
		printer->Print("return x.ServerStream.SendMsg(m)\n");
		printer->Outdent();
		printer->Print("}\n\n");
	}

}

// Generates Client method signature source
void GenerateClientMethodSignature(const grpc_generator::Method *method, grpc_generator::Printer *printer,
                                   std::map<grpc::string, grpc::string> vars) {
	vars["Method"] = exportName(method->name());
	vars["Request"] = ", in *" + ((vars["CustomMethodIO"] == "") ? method->input_name() : vars["CustomMethodIO"]);
	if (method->ClientOnlyStreaming() || method->BidiStreaming()) {
		vars["Request"] = "";
	}
	vars["Response"] = "* " + method->output_name();
	if (method->ClientOnlyStreaming() || method->BidiStreaming() || method->ServerOnlyStreaming()) {
		vars["Response"] = vars["Service"] + "_" + vars["Method"] + "Client" ;
	}
	printer->Print(vars, "$Method$(ctx $context$.Context$Request$, \n\topts... $grpc$.CallOption) ($Response$, error)");
}

// Generates Client method source
void GenerateClientMethod(const grpc_generator::Method *method, grpc_generator::Printer *printer,
                          std::map<grpc::string, grpc::string> vars) {
	printer->Print(vars, "func (c *$ServiceUnexported$Client) ");
	GenerateClientMethodSignature(method, printer, vars);
	printer->Print(" {\n");
	printer->Indent();
	vars["Method"] = exportName(method->name());
	vars["Request"] = (vars["CustomMethodIO"] == "") ? method->input_name() : vars["CustomMethodIO"];
	vars["Response"] = method->output_name();
	vars["FullMethodName"] = "/" + vars["Package"] + "." + vars["Service"] + "/" + vars["Method"];
	if (method->NoStreaming()) {
		printer->Print(vars, "out := new($Response$)\n");
		printer->Print(vars, "err := $grpc$.Invoke(ctx, \"$FullMethodName$\", in, out, c.cc, opts...)\n");
		printer->Print("if err != nil { return nil, err }\n");
		printer->Print("return out, nil\n");
		printer->Outdent();
		printer->Print("}\n\n");
		return;
	}
	vars["StreamType"] = vars["ServiceUnexported"] + vars["Method"] + "Client";
	printer->Print(vars, "stream, err := $grpc$.NewClientStream(ctx, &$MethodDesc$, c.cc, \"$FullMethodName$\", opts...)\n");
	printer->Print("if err != nil { return nil, err }\n");

	printer->Print(vars, "x := &$StreamType${stream}\n");
	if (method->ServerOnlyStreaming()) {
		printer->Print("if err := x.ClientStream.SendMsg(in); err != nil { return nil, err }\n");
		printer->Print("if err := x.ClientStream.CloseSend(); err != nil { return nil, err }\n");
	}
	printer->Print("return x,nil\n");
	printer->Outdent();
	printer->Print("}\n\n");

	bool genSend = method->BidiStreaming() || method->ClientOnlyStreaming();
	bool genRecv = method->BidiStreaming() || method->ServerOnlyStreaming();
	bool genCloseAndRecv = method->ClientOnlyStreaming();

	//Stream interface
	printer->Print(vars, "type $Service$_$Method$Client interface {\n");
	printer->Indent();
	if (genSend) {
		printer->Print(vars, "Send(*$Request$) error\n");
	}
	if (genRecv) {
		printer->Print(vars, "Recv() (*$Response$, error)\n");
	}
	if (genCloseAndRecv) {
		printer->Print(vars, "CloseAndRecv() (*$Response$, error)\n");
	}
	printer->Print(vars, "$grpc$.ClientStream\n");
	printer->Outdent();
	printer->Print("}\n\n");

	//Stream Client
	printer->Print(vars, "type $StreamType$ struct{\n");
	printer->Indent();
	printer->Print(vars, "$grpc$.ClientStream\n");
	printer->Outdent();
	printer->Print("}\n\n");

	if (genSend) {
		printer->Print(vars, "func (x *$StreamType$) Send(m *$Request$) error {\n");
		printer->Indent();
		printer->Print("return x.ClientStream.SendMsg(m)\n");
		printer->Outdent();
		printer->Print("}\n\n");
	}

	if (genRecv) {
		printer->Print(vars, "func (x *$StreamType$) Recv() (*$Response$, error) {\n");
		printer->Indent();
		printer->Print(vars, "m := new($Response$)\n");
		printer->Print("if err := x.ClientStream.RecvMsg(m); err != nil { return nil, err }\n");
		printer->Print("return m, nil\n");
		printer->Outdent();
		printer->Print("}\n\n");
	}

	if (genCloseAndRecv) {
		printer->Print(vars, "func (x *$StreamType$) CloseAndRecv() (*$Response$, error) {\n");
		printer->Indent();
		printer->Print("if err := x.ClientStream.CloseSend(); err != nil { return nil, err }\n");
		printer->Print(vars, "m := new ($Response$)\n");
		printer->Print("if err := x.ClientStream.RecvMsg(m); err != nil { return nil, err }\n");
		printer->Print("return m, nil\n");
		printer->Outdent();
		printer->Print("}\n\n");
	}
}

// Generates client API for the service
void GenerateService(const grpc_generator::Service *service, grpc_generator::Printer* printer,
                     std::map<grpc::string, grpc::string> vars) {
	vars["Service"] = exportName(service->name());
	// Client Interface
	printer->Print(vars, "// Client API for $Service$ service\n");
	printer->Print(vars, "type $Service$Client interface{\n");
	printer->Indent();
	for (int i = 0; i < service->method_count(); i++) {
		GenerateClientMethodSignature(service->method(i).get(), printer, vars);
		printer->Print("\n");
	}
	printer->Outdent();
	printer->Print("}\n\n");

	// Client structure
	vars["ServiceUnexported"] = unexportName(vars["Service"]);
	printer->Print(vars, "type $ServiceUnexported$Client struct {\n");
	printer->Indent();
	printer->Print(vars, "cc *$grpc$.ClientConn\n");
	printer->Outdent();
	printer->Print("}\n\n");

	// NewClient
	printer->Print(vars, "func New$Service$Client(cc *$grpc$.ClientConn) $Service$Client {\n");
	printer->Indent();
	printer->Print(vars, "return &$ServiceUnexported$Client{cc}");
	printer->Outdent();
	printer->Print("\n}\n\n");

	int unary_methods = 0, streaming_methods = 0;
	vars["ServiceDesc"] = "_" + vars["Service"] + "_serviceDesc";
	for (int i = 0; i < service->method_count(); i++) {
		auto method = service->method(i);
		if (method->NoStreaming()) {
			vars["MethodDesc"] = vars["ServiceDesc"] + ".Method[" + as_string(unary_methods) + "]";
			unary_methods++;
		} else {
			vars["MethodDesc"] = vars["ServiceDesc"] + ".Streams[" + as_string(streaming_methods) + "]";
			streaming_methods++;
		}
		GenerateClientMethod(method.get(), printer, vars);
	}

	//Server Interface
	printer->Print(vars, "// Server API for $Service$ service\n");
	printer->Print(vars, "type $Service$Server interface {\n");
	printer->Indent();
	for (int i = 0; i < service->method_count(); i++) {
		GenerateServerMethodSignature(service->method(i).get(), printer, vars);
		printer->Print("\n");
	}
	printer->Outdent();
	printer->Print("}\n\n");

	// Server registration.
	printer->Print(vars, "func Register$Service$Server(s *$grpc$.Server, srv $Service$Server) {\n");
	printer->Indent();
	printer->Print(vars, "s.RegisterService(&$ServiceDesc$, srv)\n");
	printer->Outdent();
	printer->Print("}\n\n");

	for (int i = 0; i < service->method_count(); i++) {
		GenerateServerMethod(service->method(i).get(), printer, vars);
		printer->Print("\n");
	}


	//Service Descriptor
	printer->Print(vars, "var $ServiceDesc$ = $grpc$.ServiceDesc{\n");
	printer->Indent();
	printer->Print(vars, "ServiceName: \"$Package$.$Service$\",\n");
	printer->Print(vars, "HandlerType: (*$Service$Server)(nil),\n");
	printer->Print(vars, "Methods: []$grpc$.MethodDesc{\n");
	printer->Indent();
	for (int i = 0; i < service->method_count(); i++) {
		auto method = service->method(i);
		vars["Method"] = method->name();
		vars["Handler"] = "_" + vars["Service"] + "_" + vars["Method"] + "_Handler";
		if (method->NoStreaming()) {
			printer->Print("{\n");
			printer->Indent();
			printer->Print(vars, "MethodName: \"$Method$\",\n");
			printer->Print(vars, "Handler: $Handler$, \n");
			printer->Outdent();
			printer->Print("},\n");
		}
	}
	printer->Outdent();
	printer->Print("},\n");
	printer->Print(vars, "Streams: []$grpc$.StreamDesc{\n");
	printer->Indent();
	for (int i = 0; i < service->method_count(); i++) {
		auto method = service->method(i);
		vars["Method"] = method->name();
		vars["Handler"] = "_" + vars["Service"] + "_" + vars["Method"] + "_Handler";
		if (!method->NoStreaming()) {
			printer->Print("{\n");
			printer->Indent();
			printer->Print(vars, "StreamName: \"$Method$\",\n");
			printer->Print(vars, "Handler: $Handler$, \n");
			if (method->ClientOnlyStreaming()) {
				printer->Print("ClientStreams: true,\n");
			} else if (method->ServerOnlyStreaming()) {
				printer->Print("ServerStreams: true,\n");
			} else {
				printer->Print("ServerStreams: true,\n");
				printer->Print("ClientStreams: true,\n");
			}
			printer->Outdent();
			printer->Print("},\n");
		}
	}
	printer->Outdent();
	printer->Print("},\n");
	printer->Outdent();
	printer->Print("}\n\n");

}


// Returns source for the service
grpc::string GenerateServiceSource(grpc_generator::File *file,
                                   const grpc_generator::Service *service,
                                   grpc_go_generator::Parameters *parameters
                                  ) {
	grpc::string out;
	auto p = file->CreatePrinter(&out);
	auto printer = p.get();
	std::map<grpc::string, grpc::string> vars;
	vars["Package"] = parameters->package_name;
	vars["grpc"] = "grpc";
	vars["context"] = "context";
	GenerateImports(file, printer, vars);
	if (parameters->custom_codec_source != "") {
		printer->Print(parameters->custom_codec_source.c_str());
	}
	if (parameters->custom_method_io_type != "") {
		vars["CustomMethodIO"] = parameters->custom_method_io_type;
	}
	GenerateService(service, printer, vars);
	return out;
}
}// Namespace grpc_go_generator